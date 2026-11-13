module

public import GraphMinor.Crossing.PlanarSubdiv
public import GraphMinor.HP25.Alternate
import GraphMinor.HP25.Lemma33

/-!
# Lemma 4: Every crossing in a planar graph uses distinct cycle bridges
(`docs/crossing/crossing_extractor.tex`, Section 5.3)

This file formalizes Section 5.3 (**Lemma 4**) of `docs/crossing/crossing_extractor.tex`:

"Suppose that a crossing \(Q,R\) has the inner vertices of both paths in the same component \(A\)
of \(K-V(D)\). Connect an inner vertex of \(Q\) to an inner vertex of \(R\) by a path inside \(A\),
and shorten it so that its inner vertices avoid \(Q\cup R\).

The cycle, the two crossing paths and this connector form a subdivision of \(K_{3,3}\). Let \(q\)
and \(r\) be the ends of the connector on \(Q\) and \(R\), and let \(q_1,r_1,q_2,r_2\) be the ends
of the crossing in cyclic order, with \(q_1,q_2\) the ends of \(Q\). The bipartition of the six
branch vertices is \(\{q_1,q_2,r\}\), \(\{r_1,r_2,q\}\). The nine branch paths are the four arcs of
the cycle, the four halves of \(Q\) and \(R\), and the connector.

This is impossible in a planar graph, by Euler's bound in Section 1. A chord already forms a
separate bridge."

**Lemma 4.** "Every crossing in a planar graph uses distinct cycle bridges. Therefore
\(\operatorname{BridgeCross}\) is complete on planar inputs."
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set GraphMinor.HP25

variable {V : Type*} {G : SimpleGraph V} {S : Set V} {D : List V}

/-! ### Path list reversal and splitting -/

/-- The reverse of a path list of `G` on `S` is a path list of `G` on `S`. -/
theorem IsPathList.reverse {l : List V} (h : IsPathList G S l) : IsPathList G S l.reverse :=
  ⟨List.nodup_reverse.mpr h.1,
    List.isChain_reverse.mpr (h.2.1.imp fun _ _ hab => hab.symm),
    fun x hx => h.2.2 x (List.mem_reverse.mp hx)⟩

/-- A prefix of a path list of `G` on `S` is a path list of `G` on `S`. -/
theorem IsPathList.of_append_left {l₁ l₂ : List V} (h : IsPathList G S (l₁ ++ l₂)) :
    IsPathList G S l₁ :=
  ⟨h.1.of_append_left, h.2.1.left_of_append, fun x hx => h.2.2 x (List.mem_append_left _ hx)⟩

/-- A suffix of a path list of `G` on `S` is a path list of `G` on `S`. -/
theorem IsPathList.of_append_right {l₁ l₂ : List V} (h : IsPathList G S (l₁ ++ l₂)) :
    IsPathList G S l₂ :=
  ⟨h.1.of_append_right, h.2.1.right_of_append, fun x hx => h.2.2 x (List.mem_append_right _ hx)⟩

/-- Splitting a `D`-path `Q : G.Walk u v` on `S` at an inner vertex `m ∈ Q.support` (`m ∉ D`) into
two path lists `L₁` (from `u` to `m`) and `L₂` (from `v` to `m`) that meet only at `m` and meet `D`
only at `u` and `v` respectively. -/
theorem split_tpath_at_inner {u v m : V} {Q : G.Walk u v} (hQ : IsTPath G D Q)
    (hQS : ∀ x ∈ Q.support, x ∈ S) (hmQ : m ∈ Q.support) (hmD : m ∉ D) :
    ∃ L₁ L₂ : List V,
      IsPathList G S L₁ ∧ IsPathList G S L₂ ∧
      (∃ mid₁, L₁ = u :: mid₁ ++ [m]) ∧ (∃ mid₂, L₂ = v :: mid₂ ++ [m]) ∧
      (∀ x ∈ L₁, x ∈ Q.support) ∧ (∀ x ∈ L₂, x ∈ Q.support) ∧
      (∀ x ∈ L₁, x ∈ L₂ → x = m) ∧
      (∀ x ∈ L₁, x ∈ D → x = u) ∧ (∀ x ∈ L₂, x ∈ D → x = v) := by
  obtain ⟨hqpath, huD, hvD, hin⟩ := hQ
  have hmu : m ≠ u := fun h => hmD (h ▸ huD)
  have hmv : m ≠ v := fun h => hmD (h ▸ hvD)
  have hP : IsPathList G S Q.support := ⟨hqpath.support_nodup, Q.isChain_adj_support, hQS⟩
  have hhead : Q.support.head? = some u := by
    rw [← Walk.cons_tail_support]; rfl
  have hlast : Q.support.getLast? = some v := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨pre, suf, heq⟩ := List.append_of_mem hmQ
  rcases pre with _ | ⟨u', mid₁⟩
  · rw [heq] at hhead
    exact absurd (Option.some.inj hhead) hmu
  have hu' : u' = u := by
    rw [heq] at hhead
    exact Option.some.inj hhead
  subst hu'
  rcases List.eq_nil_or_concat suf with rfl | ⟨mid₂, v', hcon⟩
  · rw [heq, List.getLast?_append_of_ne_nil _ (by simp)] at hlast
    exact absurd (Option.some.inj hlast) hmv
  rw [hcon, List.concat_eq_append] at heq
  have hv' : v' = v := by
    rw [heq] at hlast
    have hassoc : u' :: mid₁ ++ m :: (mid₂ ++ [v']) = (u' :: mid₁ ++ m :: mid₂) ++ [v'] := by simp
    have hlast' : (u' :: mid₁ ++ m :: (mid₂ ++ [v'])).getLast? = some v' := by
      rw [hassoc, List.getLast?_eq_some_getLast (by simp)]
      simp
    exact Option.some.inj (hlast'.symm.trans hlast)
  subst hv'
  let L₁ : List V := u' :: mid₁ ++ [m]
  let L₂r : List V := m :: mid₂ ++ [v']
  have heq₁ : Q.support = L₁ ++ (mid₂ ++ [v']) := by simp [heq, L₁]
  have heq₂ : Q.support = (u' :: mid₁) ++ L₂r := by simp [heq, L₂r]
  have hPL₁ : IsPathList G S L₁ := IsPathList.of_append_left (heq₁ ▸ hP)
  have hPL₂ : IsPathList G S L₂r.reverse :=
    IsPathList.reverse (IsPathList.of_append_right (heq₂ ▸ hP))
  have hnd : Q.support.Nodup := hP.1
  refine ⟨L₁, L₂r.reverse, hPL₁, hPL₂, ⟨mid₁, rfl⟩,
    ⟨mid₂.reverse, by simp [L₂r]⟩,
    fun x hx => heq₁ ▸ List.mem_append_left _ hx,
    fun x hx => heq₂ ▸ List.mem_append_right _ (List.mem_reverse.mp hx),
    ?_, ?_, ?_⟩
  · intro x hx1 hx2
    rw [List.mem_reverse] at hx2
    simp only [L₁, L₂r, List.mem_append, List.mem_singleton] at hx1 hx2
    rcases hx1 with hx1 | rfl
    · rcases hx2 with hx2 | rfl
      · rcases List.mem_cons.mp hx2 with rfl | hx2
        · rfl
        · have hnd' := hnd
          rw [heq] at hnd'
          exact False.elim ((List.nodup_append.mp hnd').2.2 x hx1 x
            (List.mem_cons_of_mem m (List.mem_append_left _ hx2)) rfl)
      · have hnd' := hnd
        rw [heq] at hnd'
        exact False.elim ((List.nodup_append.mp hnd').2.2 x hx1 x
          (List.mem_cons_of_mem m (List.mem_append_right _ (by simp))) rfl)
    · rfl
  · intro x hx1 hxD
    by_contra hxu
    have hxv : x = v' := by
      by_contra hxv
      exact (hin x (heq₁ ▸ List.mem_append_left _ hx1) hxu hxv).1 hxD
    subst hxv
    have hnd' := hnd
    rw [heq₁] at hnd'
    exact (List.nodup_append.mp hnd').2.2 x hx1 x (List.mem_append_right _ (by simp)) rfl
  · intro x hx2 hxD
    by_contra hxv
    have hxu : x = u' := by
      by_contra hxu
      exact (hin x (heq₂ ▸ List.mem_append_right _ (List.mem_reverse.mp hx2)) hxu hxv).1 hxD
    subst hxu
    have hnd' := hnd
    rw [heq₂] at hnd'
    exact (List.nodup_append.mp hnd').2.2 x (by simp) x (List.mem_reverse.mp hx2) rfl

/-! ### Splitting the cycle into four arcs -/

/-- Given four alternating vertices `q₁, r₁, q₂, r₂` on a cycle `D` of `G` on `S`, `D` splits into
four path lists `LD i j` (`i, j : Fin 2`) from `![q₁, q₂] i` to `![r₁, r₂] j` on `D`, meeting only
at shared endpoints. -/
theorem split_cycle_four_arcs {q₁ q₂ r₁ r₂ : V} (hD : IsCycleList G D) (hDS : ∀ v ∈ D, v ∈ S)
    (halt : Alternate D q₁ q₂ r₁ r₂) :
    q₁ ∈ D ∧ q₂ ∈ D ∧ r₁ ∈ D ∧ r₂ ∈ D ∧ q₁ ≠ q₂ ∧ r₁ ≠ r₂ ∧
    ∃ LD : Fin 2 → Fin 2 → List V,
      (∀ i j, IsPathList G S (LD i j)) ∧
      (∀ i j, ∃ mid, LD i j = (![q₁, q₂] i) :: mid ++ [![r₁, r₂] j]) ∧
      (∀ i j, ∀ x ∈ LD i j, x ∈ D) ∧
      (∀ i j i' j', (i, j) ≠ (i', j') →
        ∀ x ∈ LD i j, x ∈ LD i' j' →
          (i = i' ∧ x = ![q₁, q₂] i) ∨ (j = j' ∧ x = ![r₁, r₂] j)) := by
  obtain ⟨k, M₁, M₂, hrot, hr₁M, hr₂M⟩ := halt
  obtain ⟨A₁, B₁, rfl⟩ := List.append_of_mem hr₁M
  obtain ⟨A₂, B₂, rfl⟩ := List.append_of_mem hr₂M
  have hC' : IsCycleList G (D.rotate k) := hD.rotate k
  have hmemD : ∀ x, x ∈ D.rotate k ↔ x ∈ D := fun _ => List.mem_rotate
  have hnd : (q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂)).Nodup :=
    hrot ▸ hC'.2.1
  have hch : (q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) ++ [q₁]).IsChain G.Adj := by
    have h := hC'.2.2
    have hcons : q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) =
        q₁ :: ((A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂)) := rfl
    rw [hrot, hcons, zip_rotate_one_cons] at h
    exact isChain_iff_zip.mpr h
  have hsubD : ∀ x ∈ q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) ++ [q₁], x ∈ D := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hmemD x).mp (hrot ▸ hx)
    · simp only [List.mem_singleton] at hx
      exact (hmemD x).mp (hrot ▸ hx ▸ by simp)
  -- The four closed arcs of `D.rotate k ++ [q₁]`
  let P₀₀ : List V := q₁ :: A₁ ++ [r₁]
  let P₁₀r : List V := r₁ :: B₁ ++ [q₂]
  let P₁₁ : List V := q₂ :: A₂ ++ [r₂]
  let P₀₁r : List V := r₂ :: B₂ ++ [q₁]
  have heq₀₀ : q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) =
      P₀₀ ++ (B₁ ++ q₂ :: (A₂ ++ r₂ :: B₂)) := by simp [P₀₀]
  have heq₁₀ : q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) =
      (q₁ :: A₁) ++ P₁₀r ++ (A₂ ++ r₂ :: B₂) := by simp [P₁₀r]
  have heq₁₁ : q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) =
      (q₁ :: (A₁ ++ r₁ :: B₁)) ++ P₁₁ ++ B₂ := by simp [P₁₁]
  have heq₀₁ : q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) ++ [q₁] =
      (q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: A₂) ++ P₀₁r := by simp [P₀₁r]
  have hP_closed : ∀ {X Y Z : List V},
      X ++ Y ++ Z = q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂) ++ [q₁] →
      Y.Nodup → IsPathList G S Y := by
    intro X Y Z he hYnd
    refine ⟨hYnd, ?_, fun x hx => hDS x (hsubD x (he ▸ by simp [hx]))⟩
    have hch' := hch
    rw [← he] at hch'
    exact hch'.left_of_append.right_of_append
  have hnd₀₀ : P₀₀.Nodup := (heq₀₀ ▸ hnd).of_append_left
  have hnd₁₀ : P₁₀r.Nodup := ((heq₁₀ ▸ hnd).of_append_left).of_append_right
  have hnd₁₁ : P₁₁.Nodup := ((heq₁₁ ▸ hnd).of_append_left).of_append_right
  have hnd₀₁ : P₀₁r.Nodup := by
    have hrot2 : (q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: (A₂ ++ r₂ :: B₂)).rotate 1 =
        (A₁ ++ r₁ :: B₁ ++ q₂ :: A₂) ++ P₀₁r := by simp [P₀₁r]
    exact (hrot2 ▸ List.nodup_rotate.mpr hnd).of_append_right
  have hPL₀₀ : IsPathList G S P₀₀ :=
    hP_closed (X := []) (Z := B₁ ++ q₂ :: (A₂ ++ r₂ :: B₂) ++ [q₁]) (by simp [P₀₀]) hnd₀₀
  have hPL₁₀ : IsPathList G S P₁₀r.reverse :=
    IsPathList.reverse
      (hP_closed (X := q₁ :: A₁) (Z := A₂ ++ r₂ :: B₂ ++ [q₁]) (by simp [P₁₀r]) hnd₁₀)
  have hPL₁₁ : IsPathList G S P₁₁ :=
    hP_closed (X := q₁ :: (A₁ ++ r₁ :: B₁)) (Z := B₂ ++ [q₁]) (by simp [P₁₁]) hnd₁₁
  have hPL₀₁ : IsPathList G S P₀₁r.reverse :=
    IsPathList.reverse
      (hP_closed (X := q₁ :: (A₁ ++ r₁ :: B₁) ++ q₂ :: A₂) (Z := []) (by simp [P₀₁r]) hnd₀₁)
  let LD : Fin 2 → Fin 2 → List V := fun i j =>
    match i, j with
    | 0, 0 => P₀₀
    | 0, 1 => P₀₁r.reverse
    | 1, 0 => P₁₀r.reverse
    | 1, 1 => P₁₁
  have hq₁D : q₁ ∈ D := (hmemD q₁).mp (hrot ▸ by simp)
  have hq₂D : q₂ ∈ D := (hmemD q₂).mp (hrot ▸ by simp)
  have hr₁D : r₁ ∈ D := (hmemD r₁).mp (hrot ▸ by simp)
  have hr₂D : r₂ ∈ D := (hmemD r₂).mp (hrot ▸ by simp)
  have hq_ne : q₁ ≠ q₂ := by
    rintro rfl
    exact (List.nodup_cons.mp hnd).1 (by simp)
  have hr_ne : r₁ ≠ r₂ := by
    rintro rfl
    exact (List.nodup_append.mp hnd).2.2 r₁ (by simp) r₁ (by simp) rfl
  -- Disjointness of the 4 parts `(q₁ :: A₁)`, `(r₁ :: B₁)`, `(q₂ :: A₂)`, `(r₂ :: B₂)` in `hnd`
  have hnd4 : ((q₁ :: A₁) ++ (r₁ :: B₁) ++ (q₂ :: A₂) ++ (r₂ :: B₂)).Nodup := by
    simpa using hnd
  have hd_12 : List.Disjoint (q₁ :: A₁) (r₁ :: B₁) := fun x hx1 hx2 =>
    (List.nodup_append.mp ((hnd4.of_append_left).of_append_left)).2.2 x hx1 x hx2 rfl
  have hd_13 : List.Disjoint (q₁ :: A₁) (q₂ :: A₂) := fun x hx1 hx3 =>
    (List.nodup_append.mp (hnd4.of_append_left)).2.2 x (List.mem_append_left _ hx1) x hx3 rfl
  have hd_14 : List.Disjoint (q₁ :: A₁) (r₂ :: B₂) := fun x hx1 hx4 =>
    (List.nodup_append.mp hnd4).2.2 x (List.mem_append_left _ (List.mem_append_left _ hx1)) x hx4 rfl
  have hd_23 : List.Disjoint (r₁ :: B₁) (q₂ :: A₂) := fun x hx2 hx3 =>
    (List.nodup_append.mp (hnd4.of_append_left)).2.2 x (List.mem_append_right _ hx2) x hx3 rfl
  have hd_24 : List.Disjoint (r₁ :: B₁) (r₂ :: B₂) := fun x hx2 hx4 =>
    (List.nodup_append.mp hnd4).2.2 x (List.mem_append_left _ (List.mem_append_right _ hx2)) x hx4 rfl
  have hd_34 : List.Disjoint (q₂ :: A₂) (r₂ :: B₂) := fun x hx3 hx4 =>
    (List.nodup_append.mp hnd4).2.2 x (List.mem_append_right _ hx3) x hx4 rfl
  refine ⟨hq₁D, hq₂D, hr₁D, hr₂D, hq_ne, hr_ne, LD, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hPL₀₀
    · exact hPL₀₁
    · exact hPL₁₀
    · exact hPL₁₁
  · intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨A₁, rfl⟩
    · exact ⟨B₂.reverse, by simp [LD, P₀₁r]⟩
    · exact ⟨B₁.reverse, by simp [LD, P₁₀r]⟩
    · exact ⟨A₂, rfl⟩
  · intro i j x hx
    fin_cases i <;> fin_cases j
    · exact (hmemD x).mp (hrot ▸ heq₀₀ ▸ List.mem_append_left _ hx)
    · exact hsubD x (heq₀₁ ▸ List.mem_append_right _ (List.mem_reverse.mp hx))
    · exact (hmemD x).mp (hrot ▸ heq₁₀ ▸
        List.mem_append_left _ (List.mem_append_right _ (List.mem_reverse.mp hx)))
    · exact (hmemD x).mp (hrot ▸ heq₁₁ ▸
        List.mem_append_left _ (List.mem_append_right _ hx))
  · intro i j i' j' hne x hx1 hx2
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j'
    all_goals try exact False.elim (hne rfl)
    · -- (0, 0) vs (0, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₀₁r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_14 hx1 hx2)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hd_24 (List.mem_cons_self) hx2)
      · exact False.elim (hd_12 (List.mem_cons_self) (List.mem_cons_self))
    · -- (0, 0) vs (1, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₁₀r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_12 hx1 hx2)
      · exact False.elim (hd_13 hx1 (List.mem_cons_self))
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (hd_23 (List.mem_cons_self) (List.mem_cons_self))
    · -- (0, 0) vs (1, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₁₁, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_13 hx1 hx2)
      · exact False.elim (hd_14 hx1 (List.mem_cons_self))
      · exact False.elim (hd_23 (List.mem_cons_self) hx2)
      · exact False.elim (hd_24 (List.mem_cons_self) (List.mem_cons_self))
    · -- (0, 1) vs (0, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₀₁r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_14 hx2 hx1)
      · exact False.elim (hd_24 (List.mem_cons_self) hx1)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hd_12 (List.mem_cons_self) (List.mem_cons_self))
    · -- (0, 1) vs (1, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₁r, P₁₀r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_24 hx2 hx1)
      · exact False.elim (hd_34 (List.mem_cons_self) hx1)
      · exact False.elim (hd_12 (List.mem_cons_self) hx2)
      · exact False.elim (hd_13 (List.mem_cons_self) (List.mem_cons_self))
    · -- (0, 1) vs (1, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₁r, P₁₁, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_34 hx2 hx1)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (hd_13 (List.mem_cons_self) hx2)
      · exact False.elim (hd_14 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 0) vs (0, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₁₀r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_12 hx2 hx1)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (hd_13 hx2 (List.mem_cons_self))
      · exact False.elim (hd_23 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 0) vs (0, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₁r, P₁₀r, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_24 hx1 hx2)
      · exact False.elim (hd_12 (List.mem_cons_self) hx1)
      · exact False.elim (hd_34 (List.mem_cons_self) hx2)
      · exact False.elim (hd_13 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 0) vs (1, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₁₀r, P₁₁, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_23 hx1 hx2)
      · exact False.elim (hd_24 hx1 (List.mem_cons_self))
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hd_34 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 1) vs (0, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₀, P₁₁, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_13 hx2 hx1)
      · exact False.elim (hd_23 (List.mem_cons_self) hx1)
      · exact False.elim (hd_14 hx2 (List.mem_cons_self))
      · exact False.elim (hd_24 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 1) vs (0, 1)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₀₁r, P₁₁, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_34 hx1 hx2)
      · exact False.elim (hd_13 (List.mem_cons_self) hx1)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (hd_14 (List.mem_cons_self) (List.mem_cons_self))
    · -- (1, 1) vs (1, 0)
      simp only [Fin.zero_eta, Fin.mk_one, LD, P₁₀r, P₁₁, List.mem_reverse, List.mem_append,
        List.mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | rfl <;> rcases hx2 with hx2 | rfl
      · exact False.elim (hd_23 hx2 hx1)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (hd_24 hx2 (List.mem_cons_self))
      · exact False.elim (hd_34 (List.mem_cons_self) (List.mem_cons_self))

/-! ### Shortening the connector between `Q` and `R` -/

/-- Shortening a walk `W` avoiding `D` from `Q` to `R` yields a path list `L_conn` in `S` avoiding
`D` from some `r ∈ R.support` to some `q ∈ Q.support` that meets `Q.support` only at `q` and
`R.support` only at `r`. -/
theorem shorten_connector {q₁ q₂ r₁ r₂ u₀ v₀ : V} {Q : G.Walk q₁ q₂} {R : G.Walk r₁ r₂}
    (hdisjQR : Q.support.Disjoint R.support)
    (hu₀ : u₀ ∈ Q.support) (hv₀ : v₀ ∈ R.support)
    (W : G.Walk u₀ v₀) (hWS : ∀ x ∈ W.support, x ∈ S) (hWD : ∀ x ∈ W.support, x ∉ D) :
    ∃ (q r : V) (L_conn : List V),
      q ∈ Q.support ∧ r ∈ R.support ∧
      IsPathList G S L_conn ∧
      (∃ mid, L_conn = r :: mid ++ [q]) ∧
      (∀ x ∈ L_conn, x ∉ D) ∧
      (∀ x ∈ L_conn, x ∈ Q.support → x = q) ∧
      (∀ x ∈ L_conn, x ∈ R.support → x = r) := by
  classical
  obtain ⟨r, hrR, W₁, hW₁sub, hW₁avoidR, -⟩ :=
    exists_first_hit {x | x ∈ R.support} W hv₀
  obtain ⟨q, hqQ, W₂, hW₂sub, hW₂avoidQ, -⟩ :=
    exists_first_hit {x | x ∈ Q.support} W₁.reverse hu₀
  let P := W₂.bypass
  have hPsub₂ : ∀ x ∈ P.support, x ∈ W₂.support :=
    fun _ hx => Walk.support_bypass_subset_support W₂ hx
  have hPsub₁ : ∀ x ∈ P.support, x ∈ W₁.support :=
    fun x hx => List.mem_reverse.mp (Walk.support_reverse W₁ ▸ hW₂sub x (hPsub₂ x hx))
  have hPsubW : ∀ x ∈ P.support, x ∈ W.support :=
    fun x hx => hW₁sub x (hPsub₁ x hx)
  have hrq : r ≠ q := fun h => hdisjQR hqQ (h ▸ hrR)
  have hPpath : IsPathList G S P.support :=
    ⟨W₂.bypass_isPath.support_nodup, P.isChain_adj_support, fun x hx => hWS x (hPsubW x hx)⟩
  obtain ⟨mid, hmid⟩ : ∃ mid, P.support = r :: mid ++ [q] := by
    have hlast : P.support.getLast? = some q := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    have hcons := (Walk.cons_tail_support P).symm
    rcases List.eq_nil_or_concat P.support.tail with h | ⟨mid, q', hcon⟩
    · rw [h] at hcons
      rw [hcons] at hlast
      exact absurd (Option.some.inj hlast) hrq
    · rw [hcon, List.concat_eq_append] at hcons
      rw [hcons] at hlast
      have hlast' : (r :: (mid ++ [q'])).getLast? = some q' := by
        show ((r :: mid) ++ [q']).getLast? = some q'
        rw [List.getLast?_eq_some_getLast (by simp)]
        simp
      have hq' : q' = q := Option.some.inj (hlast'.symm.trans hlast)
      subst hq'
      exact ⟨mid, by simpa using hcons⟩
  refine ⟨q, r, P.support, hqQ, hrR, hPpath, ⟨mid, hmid⟩,
    fun x hx => hWD x (hPsubW x hx),
    fun x hx hxQ => by_contra fun hxq => hW₂avoidQ x (hPsub₂ x hx) hxq hxQ,
    fun x hx hxR => by_contra fun hxr => hW₁avoidR x (hPsub₁ x hx) hxr hxR⟩

/-! ### Lemma 4 -/

/-- **Lemma 4** (`docs/crossing/crossing_extractor.tex`, Section 5.3):
"Every crossing in a planar graph uses distinct cycle bridges."

If `G` is planar on `S`, `D` is a cycle of `G` in `S`, and `Q, R` is a crossing of `D` in `G` on
`S`, then no walk `W` of `G` in `S` avoiding `D` connects a vertex of `Q` to a vertex of `R`. -/
theorem lemma_4 {q₁ q₂ r₁ r₂ u₀ v₀ : V} {Q : G.Walk q₁ q₂} {R : G.Walk r₁ r₂}
    (hP : Nonempty (PlaneEmbedding G S))
    (hD : IsCycleList G D) (hDS : ∀ v ∈ D, v ∈ S)
    (hcross : IsCrossing G D Q R)
    (hQS : ∀ x ∈ Q.support, x ∈ S) (hRS : ∀ x ∈ R.support, x ∈ S)
    (hu₀ : u₀ ∈ Q.support) (hv₀ : v₀ ∈ R.support)
    (W : G.Walk u₀ v₀) (hWS : ∀ x ∈ W.support, x ∈ S) (hWD : ∀ x ∈ W.support, x ∉ D) :
    False := by
  have halt := IsCrossing.alternate hcross
  obtain ⟨_, hQ, hR, hdisjQR⟩ := hcross
  obtain ⟨q, r, L_conn, hqQ, hrR, hPconn, ⟨mid_conn, hmid_conn⟩, hconnD, hconnQ, hconnR⟩ :=
    shorten_connector hdisjQR hu₀ hv₀ W hWS hWD
  have hqD : q ∉ D := hconnD q (by simp [hmid_conn])
  have hrD : r ∉ D := hconnD r (by simp [hmid_conn])
  obtain ⟨LQ₁, LQ₂, hPLQ₁, hPLQ₂, ⟨midQ₁, hmidQ₁⟩, ⟨midQ₂, hmidQ₂⟩,
    hLQ₁sub, hLQ₂sub, hLQinter, hLQ₁D, hLQ₂D⟩ :=
    split_tpath_at_inner hQ hQS hqQ hqD
  obtain ⟨LR₁, LR₂, hPLR₁, hPLR₂, ⟨midR₁, hmidR₁⟩, ⟨midR₂, hmidR₂⟩,
    hLR₁sub, hLR₂sub, hLRinter, hLR₁D, hLR₂D⟩ :=
    split_tpath_at_inner hR hRS hrR hrD
  obtain ⟨hq₁D, hq₂D, hr₁D, hr₂D, hq_ne, hr_ne, LD, hPLD, hendsLD, hLDsub, hLDdisj⟩ :=
    split_cycle_four_arcs hD hDS halt
  -- The 6 branch vertices `a = ![q₁, q₂, r]` and `b = ![r₁, r₂, q]`
  let a : Fin 3 → V := ![q₁, q₂, r]
  let b : Fin 3 → V := ![r₁, r₂, q]
  have hainj : Function.Injective a := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp [a] at he ⊢
    · exact absurd he hq_ne
    · exact absurd (he ▸ hq₁D) hrD
    · exact absurd he.symm hq_ne
    · exact absurd (he ▸ hq₂D) hrD
    · exact absurd (he ▸ hq₁D) hrD
    · exact absurd (he ▸ hq₂D) hrD
  have hbinj : Function.Injective b := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp [b] at he ⊢
    · exact absurd he hr_ne
    · exact absurd (he ▸ hr₁D) hqD
    · exact absurd he.symm hr_ne
    · exact absurd (he ▸ hr₂D) hqD
    · exact absurd (he ▸ hr₁D) hqD
    · exact absurd (he ▸ hr₂D) hqD
  have hab : ∀ i j, a i ≠ b j := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp [a, b] at he
    · exact hdisjQR (Walk.start_mem_support Q) (he ▸ Walk.start_mem_support R)
    · exact hdisjQR (Walk.start_mem_support Q) (he ▸ Walk.end_mem_support R)
    · exact hqD (he ▸ hq₁D)
    · exact hdisjQR (Walk.end_mem_support Q) (he ▸ Walk.start_mem_support R)
    · exact hdisjQR (Walk.end_mem_support Q) (he ▸ Walk.end_mem_support R)
    · exact hqD (he ▸ hq₂D)
    · exact hrD (he ▸ hr₁D)
    · exact hrD (he ▸ hr₂D)
    · exact hdisjQR (he ▸ hqQ) hrR
  -- The 9 branch paths `L i j` from `a i` to `b j`
  let L : Fin 3 → Fin 3 → List V := fun i j =>
    match i, j with
    | 0, 0 => LD 0 0
    | 0, 1 => LD 0 1
    | 0, 2 => LQ₁
    | 1, 0 => LD 1 0
    | 1, 1 => LD 1 1
    | 1, 2 => LQ₂
    | 2, 0 => LR₁.reverse
    | 2, 1 => LR₂.reverse
    | 2, 2 => L_conn
  refine not_planar_of_K33_subdivision (a := a) (b := b) (L := L)
    hainj hbinj hab ?_ ?_ ?_ hP
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hPLD 0 0
    · exact hPLD 0 1
    · exact hPLQ₁
    · exact hPLD 1 0
    · exact hPLD 1 1
    · exact hPLQ₂
    · exact IsPathList.reverse hPLR₁
    · exact IsPathList.reverse hPLR₂
    · exact hPconn
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hendsLD 0 0
    · exact hendsLD 0 1
    · exact ⟨midQ₁, hmidQ₁⟩
    · exact hendsLD 1 0
    · exact hendsLD 1 1
    · exact ⟨midQ₂, hmidQ₂⟩
    · exact ⟨midR₁.reverse, by simp [L, a, b, hmidR₁]⟩
    · exact ⟨midR₂.reverse, by simp [L, a, b, hmidR₂]⟩
    · exact ⟨mid_conn, hmid_conn⟩
  · -- Helper facts for each group of paths
    have hD_Q₁ : ∀ (i₀ j₀ : Fin 2) x, x ∈ LD i₀ j₀ → x ∈ LQ₁ → i₀ = 0 ∧ x = q₁ := by
      intro i₀ j₀ x hxD hxQ
      rcases hLQ₁D x hxQ (hLDsub i₀ j₀ x hxD) with rfl
      fin_cases i₀ <;> fin_cases j₀
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · obtain ⟨m, hm⟩ := hendsLD 0 0
        rcases hLDdisj 0 0 1 0 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨-, h2⟩
        · exact False.elim (Fin.zero_ne_one hcon)
        · exact False.elim (hab 0 0 h2)
      · obtain ⟨m, hm⟩ := hendsLD 0 0
        rcases hLDdisj 0 0 1 1 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨hcon, -⟩ <;>
          exact False.elim (Fin.zero_ne_one hcon)
    have hD_Q₂ : ∀ (i₀ j₀ : Fin 2) x, x ∈ LD i₀ j₀ → x ∈ LQ₂ → i₀ = 1 ∧ x = q₂ := by
      intro i₀ j₀ x hxD hxQ
      rcases hLQ₂D x hxQ (hLDsub i₀ j₀ x hxD) with rfl
      fin_cases i₀ <;> fin_cases j₀
      · obtain ⟨m, hm⟩ := hendsLD 1 0
        rcases hLDdisj 1 0 0 0 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨-, h2⟩
        · exact False.elim (Fin.zero_ne_one hcon.symm)
        · exact False.elim (hab 1 0 h2)
      · obtain ⟨m, hm⟩ := hendsLD 1 0
        rcases hLDdisj 1 0 0 1 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨hcon, -⟩
        · exact False.elim (Fin.zero_ne_one hcon.symm)
        · exact False.elim (Fin.zero_ne_one hcon)
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    have hD_R₁ : ∀ (i₀ j₀ : Fin 2) x, x ∈ LD i₀ j₀ → x ∈ LR₁.reverse → j₀ = 0 ∧ x = r₁ := by
      intro i₀ j₀ x hxD hxR
      rcases hLR₁D x (List.mem_reverse.mp hxR) (hLDsub i₀ j₀ x hxD) with rfl
      fin_cases i₀ <;> fin_cases j₀
      · exact ⟨rfl, rfl⟩
      · obtain ⟨m, hm⟩ := hendsLD 0 0
        rcases hLDdisj 0 0 0 1 (by decide) x (by simp [hm]) hxD with ⟨-, h1⟩ | ⟨hcon, -⟩
        · exact False.elim (hab 0 0 h1.symm)
        · exact False.elim (Fin.zero_ne_one hcon)
      · exact ⟨rfl, rfl⟩
      · obtain ⟨m, hm⟩ := hendsLD 0 0
        rcases hLDdisj 0 0 1 1 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨hcon, -⟩ <;>
          exact False.elim (Fin.zero_ne_one hcon)
    have hD_R₂ : ∀ (i₀ j₀ : Fin 2) x, x ∈ LD i₀ j₀ → x ∈ LR₂.reverse → j₀ = 1 ∧ x = r₂ := by
      intro i₀ j₀ x hxD hxR
      rcases hLR₂D x (List.mem_reverse.mp hxR) (hLDsub i₀ j₀ x hxD) with rfl
      fin_cases i₀ <;> fin_cases j₀
      · obtain ⟨m, hm⟩ := hendsLD 0 1
        rcases hLDdisj 0 1 0 0 (by decide) x (by simp [hm]) hxD with ⟨-, h1⟩ | ⟨hcon, -⟩
        · exact False.elim (hab 0 1 h1.symm)
        · exact False.elim (Fin.zero_ne_one hcon.symm)
      · exact ⟨rfl, rfl⟩
      · obtain ⟨m, hm⟩ := hendsLD 0 1
        rcases hLDdisj 0 1 1 0 (by decide) x (by simp [hm]) hxD with ⟨hcon, -⟩ | ⟨hcon, -⟩
        · exact False.elim (Fin.zero_ne_one hcon)
        · exact False.elim (Fin.zero_ne_one hcon.symm)
      · exact ⟨rfl, rfl⟩
    intro i j i' j' hne x hx1 hx2
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j'
    all_goals try exact False.elim (hne rfl)
    -- Cycle arc vs Cycle arc (12 cases)
    · rcases hLDdisj 0 0 0 1 (by decide) x hx1 hx2 with ⟨_, h⟩ | ⟨hcon, _⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨_, h⟩ := hD_Q₁ 0 0 x hx1 hx2; exact Or.inl ⟨rfl, h⟩
    · rcases hLDdisj 0 0 1 0 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨_, h⟩
      · exact False.elim (Fin.zero_ne_one hcon)
      · exact Or.inr ⟨rfl, h⟩
    · rcases hLDdisj 0 0 1 1 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨hcon, _⟩ <;>
        exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨hcon, _⟩ := hD_Q₂ 0 0 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨_, h⟩ := hD_R₁ 0 0 x hx1 hx2; exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_R₂ 0 0 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon)
    · exact False.elim (hconnD x hx2 (hLDsub 0 0 x hx1))
    -- (0, 1) vs others
    · rcases hLDdisj 0 1 0 0 (by decide) x hx1 hx2 with ⟨_, h⟩ | ⟨hcon, _⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact False.elim (Fin.zero_ne_one hcon.symm)
    · obtain ⟨_, h⟩ := hD_Q₁ 0 1 x hx1 hx2; exact Or.inl ⟨rfl, h⟩
    · rcases hLDdisj 0 1 1 0 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨hcon, _⟩
      · exact False.elim (Fin.zero_ne_one hcon)
      · exact False.elim (Fin.zero_ne_one hcon.symm)
    · rcases hLDdisj 0 1 1 1 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨_, h⟩
      · exact False.elim (Fin.zero_ne_one hcon)
      · exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_Q₂ 0 1 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨hcon, _⟩ := hD_R₁ 0 1 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon.symm)
    · obtain ⟨_, h⟩ := hD_R₂ 0 1 x hx1 hx2; exact Or.inr ⟨rfl, h⟩
    · exact False.elim (hconnD x hx2 (hLDsub 0 1 x hx1))
    -- (0, 2) = LQ₁ vs others
    · obtain ⟨_, h⟩ := hD_Q₁ 0 0 x hx2 hx1; exact Or.inl ⟨rfl, h⟩
    · obtain ⟨_, h⟩ := hD_Q₁ 0 1 x hx2 hx1; exact Or.inl ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_Q₁ 1 0 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon.symm)
    · obtain ⟨hcon, _⟩ := hD_Q₁ 1 1 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon.symm)
    · exact Or.inr ⟨rfl, hLQinter x hx1 hx2⟩
    · exact False.elim (hdisjQR (hLQ₁sub x hx1) (hLR₁sub x (List.mem_reverse.mp hx2)))
    · exact False.elim (hdisjQR (hLQ₁sub x hx1) (hLR₂sub x (List.mem_reverse.mp hx2)))
    · exact Or.inr ⟨rfl, hconnQ x hx2 (hLQ₁sub x hx1)⟩
    -- (1, 0) vs others
    · rcases hLDdisj 1 0 0 0 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨_, h⟩
      · exact False.elim (Fin.zero_ne_one hcon.symm)
      · exact Or.inr ⟨rfl, h⟩
    · rcases hLDdisj 1 0 0 1 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨hcon, _⟩
      · exact False.elim (Fin.zero_ne_one hcon.symm)
      · exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨hcon, _⟩ := hD_Q₁ 1 0 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon.symm)
    · rcases hLDdisj 1 0 1 1 (by decide) x hx1 hx2 with ⟨_, h⟩ | ⟨hcon, _⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨_, h⟩ := hD_Q₂ 1 0 x hx1 hx2; exact Or.inl ⟨rfl, h⟩
    · obtain ⟨_, h⟩ := hD_R₁ 1 0 x hx1 hx2; exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_R₂ 1 0 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon)
    · exact False.elim (hconnD x hx2 (hLDsub 1 0 x hx1))
    -- (1, 1) vs others
    · rcases hLDdisj 1 1 0 0 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨hcon, _⟩ <;>
        exact False.elim (Fin.zero_ne_one hcon.symm)
    · rcases hLDdisj 1 1 0 1 (by decide) x hx1 hx2 with ⟨hcon, _⟩ | ⟨_, h⟩
      · exact False.elim (Fin.zero_ne_one hcon.symm)
      · exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_Q₁ 1 1 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon.symm)
    · rcases hLDdisj 1 1 1 0 (by decide) x hx1 hx2 with ⟨_, h⟩ | ⟨hcon, _⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact False.elim (Fin.zero_ne_one hcon.symm)
    · obtain ⟨_, h⟩ := hD_Q₂ 1 1 x hx1 hx2; exact Or.inl ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_R₁ 1 1 x hx1 hx2; exact False.elim (Fin.zero_ne_one hcon.symm)
    · obtain ⟨_, h⟩ := hD_R₂ 1 1 x hx1 hx2; exact Or.inr ⟨rfl, h⟩
    · exact False.elim (hconnD x hx2 (hLDsub 1 1 x hx1))
    -- (1, 2) = LQ₂ vs others
    · obtain ⟨hcon, _⟩ := hD_Q₂ 0 0 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨hcon, _⟩ := hD_Q₂ 0 1 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon)
    · exact Or.inr ⟨rfl, hLQinter x hx2 hx1⟩
    · obtain ⟨_, h⟩ := hD_Q₂ 1 0 x hx2 hx1; exact Or.inl ⟨rfl, h⟩
    · obtain ⟨_, h⟩ := hD_Q₂ 1 1 x hx2 hx1; exact Or.inl ⟨rfl, h⟩
    · exact False.elim (hdisjQR (hLQ₂sub x hx1) (hLR₁sub x (List.mem_reverse.mp hx2)))
    · exact False.elim (hdisjQR (hLQ₂sub x hx1) (hLR₂sub x (List.mem_reverse.mp hx2)))
    · exact Or.inr ⟨rfl, hconnQ x hx2 (hLQ₂sub x hx1)⟩
    -- (2, 0) = LR₁.reverse vs others
    · obtain ⟨_, h⟩ := hD_R₁ 0 0 x hx2 hx1; exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_R₁ 0 1 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon.symm)
    · exact False.elim (hdisjQR (hLQ₁sub x hx2) (hLR₁sub x (List.mem_reverse.mp hx1)))
    · obtain ⟨_, h⟩ := hD_R₁ 1 0 x hx2 hx1; exact Or.inr ⟨rfl, h⟩
    · obtain ⟨hcon, _⟩ := hD_R₁ 1 1 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon.symm)
    · exact False.elim (hdisjQR (hLQ₂sub x hx2) (hLR₁sub x (List.mem_reverse.mp hx1)))
    · exact Or.inl ⟨rfl, hLRinter x (List.mem_reverse.mp hx1) (List.mem_reverse.mp hx2)⟩
    · exact Or.inl ⟨rfl, hconnR x hx2 (hLR₁sub x (List.mem_reverse.mp hx1))⟩
    -- (2, 1) = LR₂.reverse vs others
    · obtain ⟨hcon, _⟩ := hD_R₂ 0 0 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨_, h⟩ := hD_R₂ 0 1 x hx2 hx1; exact Or.inr ⟨rfl, h⟩
    · exact False.elim (hdisjQR (hLQ₁sub x hx2) (hLR₂sub x (List.mem_reverse.mp hx1)))
    · obtain ⟨hcon, _⟩ := hD_R₂ 1 0 x hx2 hx1; exact False.elim (Fin.zero_ne_one hcon)
    · obtain ⟨_, h⟩ := hD_R₂ 1 1 x hx2 hx1; exact Or.inr ⟨rfl, h⟩
    · exact False.elim (hdisjQR (hLQ₂sub x hx2) (hLR₂sub x (List.mem_reverse.mp hx1)))
    · exact Or.inl ⟨rfl, hLRinter x (List.mem_reverse.mp hx2) (List.mem_reverse.mp hx1)⟩
    · exact Or.inl ⟨rfl, hconnR x hx2 (hLR₂sub x (List.mem_reverse.mp hx1))⟩
    -- (2, 2) = L_conn vs others
    · exact False.elim (hconnD x hx1 (hLDsub 0 0 x hx2))
    · exact False.elim (hconnD x hx1 (hLDsub 0 1 x hx2))
    · exact Or.inr ⟨rfl, hconnQ x hx1 (hLQ₁sub x hx2)⟩
    · exact False.elim (hconnD x hx1 (hLDsub 1 0 x hx2))
    · exact False.elim (hconnD x hx1 (hLDsub 1 1 x hx2))
    · exact Or.inr ⟨rfl, hconnQ x hx1 (hLQ₂sub x hx2)⟩
    · exact Or.inl ⟨rfl, hconnR x hx1 (hLR₁sub x (List.mem_reverse.mp hx2))⟩
    · exact Or.inl ⟨rfl, hconnR x hx1 (hLR₂sub x (List.mem_reverse.mp hx2))⟩

/-- **Lemma 4 (single-chord case)**: if a `D`-path `Q : G.Walk q₁ q₂` has length at most `1`
(a single chord), it has no inner vertices (`∀ x ∈ Q.support, x = q₁ ∨ x = q₂`), and every vertex
of `Q` lies in `D`. Consequently, no walk avoiding `D` meets `Q`. -/
theorem chord_no_inner {q₁ q₂ : V} {Q : G.Walk q₁ q₂} (hQ : IsTPath G D Q) (hlen : Q.length ≤ 1) :
    (∀ x ∈ Q.support, x = q₁ ∨ x = q₂) ∧ (∀ x ∈ Q.support, x ∈ D) := by
  have hends : ∀ x ∈ Q.support, x = q₁ ∨ x = q₂ := by
    rcases Q with _ | ⟨h1, _ | ⟨_, _⟩⟩
    · intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact Or.inl hx
    · intro x hx
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      exact hx
    · simp only [Walk.length_cons] at hlen
      omega
  refine ⟨hends, fun x hx => ?_⟩
  rcases hends x hx with rfl | rfl
  · exact hQ.2.1
  · exact hQ.2.2.1

end GraphMinor.Crossing
