module

public import GraphMinor.GM08.Section11Seq
public import GraphMinor.GM08.Section11Cylinder

/-!
# The contraction of a sleeve onto the cylinder

This file does the combinatorial part of contracting a sleeve onto the `r × s` cylinder in the
proof of Graph Minors VIII, (11.1) (page 273). A sleeve is given here by sequences
(`SleeveSeq`): its circuits `C_1, …, C_s` (`c j`, of period `n j`, with `C_1` innermost) and its
radial paths `P_1, …, P_r` (`d i k` for `k ≤ len i`, from `C_1` to the vertex `d i (len i)` on the
O-arc). The radial path `P_i` first meets `C_j` at `hit i j`, and it meets `C_j` before it meets
any later circuit (`level`). Each `P_i ∩ C_j` is an interval of `C_j` (`arc`).

A position on a circuit is *owned* by the radial path of the last radial-path vertex at or before
it (`SleeveSeq.owner`). The branch set of the cylinder vertex `(k, j)` is the part of the radial path
`P_{σ k}` from `C_j` up to just before `C_{j + 1}`, together with the positions of `C_j` owned by
`P_{σ k}` (`SleeveSeq.branch`). Here `σ` lists the radial paths in the order in which they meet
`C_1` (`SleeveSeq.exists_order`). For these branch sets to give the edges of the circles of the
cylinder, the radial paths must meet every circuit in the same cyclic order. This is a fact of the
plane, proved in `GraphMinor/GM08/Section11Order.lean`; here it is the hypothesis that two radial
paths consecutive on `C_j` are consecutive on `C_{j + 1}`. With it, the strengthened III (3.8)
applies (`SleeveSeq.exists_decomposition`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph Surface GM03 GM06

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

/-- A sleeve given by sequences: the circuits `c j` (period `n j`), the radial paths `d i`
(`d i 0, …, d i (len i)`), and the first position `hit i j` of `d i` on the circuit `c j`. -/
structure SleeveSeq (G : Graph α β) (r s : ℕ) where
  /-- The length of the circuit `C_j`. -/
  n : Fin s → ℕ
  n_pos : ∀ j, 0 < n j
  /-- The vertices of the circuit `C_j`, repeating with period `n j`. -/
  c : Fin s → ℕ → α
  /-- The edges of the circuit `C_j`: `ε j x` joins `c j x` and `c j (x + 1)`. -/
  ε : Fin s → ℕ → β
  c_mod : ∀ j x, c j (x % n j) = c j x
  c_link : ∀ j x, G.IsLink (ε j x) (c j x) (c j (x + 1))
  c_inj : ∀ j x y, x < n j → y < n j → c j x = c j y → x = y
  c_disj : ∀ j j' x y, j ≠ j' → c j x ≠ c j' y
  /-- The length of the radial path `P_i`. -/
  len : Fin r → ℕ
  /-- The vertices of the radial path `P_i`. -/
  d : Fin r → ℕ → α
  /-- The edges of the radial path `P_i`: `δ i k` joins `d i k` and `d i (k + 1)`. -/
  δ : Fin r → ℕ → β
  d_mem : ∀ i k, k ≤ len i → d i k ∈ V(G)
  d_link : ∀ i k, k < len i → G.IsLink (δ i k) (d i k) (d i (k + 1))
  d_inj : ∀ i k k', k ≤ len i → k' ≤ len i → d i k = d i k' → k = k'
  d_disj : ∀ i i' k k', i ≠ i' → k ≤ len i → k' ≤ len i' → d i k ≠ d i' k'
  /-- The first position of `P_i` on `C_j`. -/
  hit : Fin r → Fin s → ℕ
  hit_le : ∀ i j, hit i j ≤ len i
  hit_mem : ∀ i j, ∃ x, c j x = d i (hit i j)
  hit_min : ∀ i j k, k < hit i j → ∀ x, c j x ≠ d i k
  /-- `P_i` meets `C_j` before it meets any later circuit. -/
  level : ∀ i j j' k x, k ≤ len i → d i k = c j x → j < j' → k < hit i j'
  /-- `P_i ∩ C_j` is an interval of `C_j`: if it has a position strictly between two positions
  `z < y` not on `P_i`, then all of it is strictly between them. -/
  arc : ∀ i j z y, z < y → (∀ k ≤ len i, d i k ≠ c j z) → (∀ k ≤ len i, d i k ≠ c j y) →
    ∀ x, z < x → x < y → (∃ k ≤ len i, d i k = c j x) →
    ∀ x' k', k' ≤ len i → d i k' = c j x' → ∃ x'', z < x'' ∧ x'' < y ∧ c j x'' = c j x'

namespace SleeveSeq

variable {G : Graph α β} {r s : ℕ} (L : SleeveSeq G r s)

/-- `u` is a vertex of the radial path `P_i`. -/
@[expose] def OnSpoke (i : Fin r) (u : α) : Prop := ∃ k ≤ L.len i, L.d i k = u

/-- The vertices of the radial paths. -/
@[expose] def marked : Set α := {u | ∃ i, L.OnSpoke i u}

/-- The radial path through `u`, if there is one. -/
@[expose] noncomputable def lab (u : α) : Option (Fin r) := by
  classical
  exact if h : ∃ i, L.OnSpoke i u then some h.choose else none

/-- The owner of the position `x` of `C_j`. -/
@[expose] noncomputable def owner (j : Fin s) (x : ℕ) : Option (Fin r) :=
  ownerIdx (L.n j) (L.c j) L.marked L.lab x

/-- The radial paths `P_a` and `P_b` are consecutive on `C_j`: the owner changes between them. -/
@[expose] def Adj (j : Fin s) (a b : Fin r) : Prop :=
  ∃ x, (L.owner j x = some a ∧ L.owner j (x + 1) = some b) ∨
    (L.owner j x = some b ∧ L.owner j (x + 1) = some a)

variable {L}

theorem OnSpoke.eq {i i' : Fin r} {u : α} (h : L.OnSpoke i u) (h' : L.OnSpoke i' u) : i = i' := by
  by_contra hne
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨k', hk', he⟩ := h'
  exact L.d_disj i i' k k' hne hk hk' he.symm

theorem lab_eq {i : Fin r} {u : α} (h : L.OnSpoke i u) : L.lab u = some i := by
  classical
  have hex : ∃ i, L.OnSpoke i u := ⟨i, h⟩
  simp only [lab]
  rw [dite_eq_left hex, hex.choose_spec.eq h]

theorem onSpoke_of_lab {i : Fin r} {u : α} (h : L.lab u = some i) : L.OnSpoke i u := by
  classical
  by_cases hex : ∃ i, L.OnSpoke i u
  · obtain ⟨i', hi'⟩ := hex
    rw [lab_eq hi'] at h
    cases h
    exact hi'
  · simp only [lab] at h
    rw [dite_eq_right hex] at h
    cases h

theorem c_mem (j : Fin s) (x : ℕ) : L.c j x ∈ V(G) := (L.c_link j x).left_mem

theorem c_add (j : Fin s) (x : ℕ) : L.c j (x + L.n j) = L.c j x :=
  seq_add_period (L.c_mod j) x

theorem mod_eq_of_c_eq {j : Fin s} {x y : ℕ} (h : L.c j x = L.c j y) : x % L.n j = y % L.n j :=
  seq_mod_eq_of_eq (L.n_pos j) (L.c_mod j) (L.c_inj j) h

/-- Two positions in one window of length `n j` with the same vertex are equal. -/
theorem eq_of_c_eq_window {j : Fin s} {x₀ a b : ℕ} (ha : a < L.n j) (hb : b < L.n j)
    (h : L.c j (x₀ + a) = L.c j (x₀ + b)) : a = b := by
  have h1 := L.mod_eq_of_c_eq h
  have h2 : a ≡ b [MOD L.n j] := Nat.ModEq.add_left_cancel' x₀ h1
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

/-- Every vertex of `C_j` is at some position of every window of length `n j`. -/
theorem exists_offset (j : Fin s) (x₀ x : ℕ) : ∃ y, y < L.n j ∧ L.c j (x₀ + y) = L.c j x := by
  have hn := L.n_pos j
  set m := x + L.n j - x₀ % L.n j with hm
  have hx₀ := Nat.mod_lt x₀ hn
  refine ⟨(x % L.n j + L.n j - x₀ % L.n j) % L.n j, Nat.mod_lt _ hn, ?_⟩
  refine seq_mod_eq (L.c_mod j) ?_
  have hxn := Nat.mod_lt x hn
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have : x₀ % L.n j + (x % L.n j + L.n j - x₀ % L.n j) = x % L.n j + L.n j := by omega
  rw [← Nat.mod_add_mod x₀, this, Nat.add_mod_right, Nat.mod_mod]

variable (hr : 0 < r)
include hr

theorem exists_marked (j : Fin s) : ∃ x, L.c j x ∈ L.marked := by
  obtain ⟨x, hx⟩ := L.hit_mem ⟨0, hr⟩ j
  exact ⟨x, ⟨0, hr⟩, L.hit ⟨0, hr⟩ j, L.hit_le ⟨0, hr⟩ j, hx.symm⟩

theorem owner_of_onSpoke {j : Fin s} {x : ℕ} {i : Fin r} (h : L.OnSpoke i (L.c j x)) :
    L.owner j x = some i := by
  rw [owner, ownerIdx_of_mem (L.n_pos j) (L.c_mod j) (L.exists_marked hr j) L.lab ⟨i, h⟩,
    lab_eq h]

theorem owner_succ {j : Fin s} {x : ℕ} (h : L.c j (x + 1) ∉ L.marked) :
    L.owner j (x + 1) = L.owner j x :=
  ownerIdx_succ (L.n_pos j) (L.c_mod j) (L.exists_marked hr j) L.lab h

theorem owner_eq_of_c_eq {j : Fin s} {x y : ℕ} (h : L.c j x = L.c j y) :
    L.owner j x = L.owner j y :=
  ownerIdx_mod (L.n_pos j) (L.c_mod j) (L.exists_marked hr j) L.lab (L.mod_eq_of_c_eq h)

theorem owner_isSome (j : Fin s) (x : ℕ) : ∃ i, L.owner j x = some i := by
  obtain ⟨-, hmem, -⟩ := backIdx_spec (L.n_pos j) (L.c_mod j) (L.exists_marked hr j) x
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, by simp only [owner, ownerIdx]; exact lab_eq hi⟩

/-- If the owner changes at `x + 1`, then `c j (x + 1)` is on the radial path that owns it. -/
theorem onSpoke_of_owner_ne {j : Fin s} {x : ℕ} {i : Fin r} (hne : L.owner j x ≠ L.owner j (x + 1))
    (hi : L.owner j (x + 1) = some i) : L.OnSpoke i (L.c j (x + 1)) := by
  have hm := mem_of_ownerIdx_ne (L.n_pos j) (L.c_mod j) (L.exists_marked hr j) L.lab hne
  obtain ⟨i', hi'⟩ := hm
  rw [owner_of_onSpoke hr hi'] at hi
  cases hi
  exact hi'

/-! ## The order of the radial paths on one circuit -/

omit hr in
/-- Some position of `C_j` is on `P_e` while the position before it is not. -/
theorem exists_start {j : Fin s} {e e' : Fin r} (hne : e ≠ e') {p q : ℕ}
    (hp : L.OnSpoke e (L.c j p)) (hq : L.OnSpoke e' (L.c j q)) :
    ∃ x₀, L.OnSpoke e (L.c j x₀) ∧ ¬ L.OnSpoke e (L.c j (x₀ + L.n j - 1)) := by
  classical
  have hn := L.n_pos j
  obtain ⟨y, hy, hyq⟩ := L.exists_offset j (p % L.n j + 1) q
  have hex : ∃ t, ¬ L.OnSpoke e (L.c j (p % L.n j + L.n j - t)) := by
    refine ⟨L.n j - 1 - y, ?_⟩
    have hp' := Nat.mod_lt p hn
    rw [show p % L.n j + L.n j - (L.n j - 1 - y) = p % L.n j + 1 + y by omega, hyq]
    exact fun h => hne (h.eq hq)
  set t := Nat.find hex
  have ht0 : t ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0, Nat.sub_zero, L.c_add, L.c_mod] at this
    exact this hp
  have hmin := Nat.find_min hex (show t - 1 < t by omega)
  push Not at hmin
  have htn : t ≤ p % L.n j + L.n j := by
    by_contra hlt
    have h1 : ¬ L.OnSpoke e (L.c j (p % L.n j + L.n j - t)) := Nat.find_spec hex
    have h2 := Nat.find_min hex (show p % L.n j + L.n j < t by omega)
    push Not at h2
    rw [show p % L.n j + L.n j - (p % L.n j + L.n j) = p % L.n j + L.n j - t by omega] at h2
    exact h1 h2
  refine ⟨p % L.n j + L.n j - (t - 1), hmin, ?_⟩
  have := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (p % L.n j + L.n j - t) with h0 | hpos
  · -- The position before `0` is `n j - 1`.
    have heq : p % L.n j + L.n j - (t - 1) = 1 := by omega
    rw [heq, show 1 + L.n j - 1 = L.n j by omega, ← L.c_mod j (L.n j), Nat.mod_self]
    rwa [h0] at this
  · rw [show p % L.n j + L.n j - (t - 1) + L.n j - 1 = p % L.n j + L.n j - t + L.n j by omega,
      L.c_add]
    exact this

/-- The radial paths in the order in which they meet `C_j`: consecutive ones in this order are
consecutive on `C_j`, and so are the last and the first. -/
theorem exists_order (j : Fin s) :
    ∃ σ : Equiv.Perm (Fin r), ∀ k : Fin r, σ k ≠ σ (nextSpoke k) →
      L.Adj j (σ k) (σ (nextSpoke k)) := by
  classical
  by_cases hr1 : r ≤ 1
  · refine ⟨1, fun k hk => absurd ?_ hk⟩
    have : nextSpoke k = k := Fin.ext (by have := k.2; simp only [nextSpoke]; omega)
    rw [this]
  push Not at hr1
  have hn := L.n_pos j
  set e₁ : Fin r := ⟨0, hr⟩
  set e₂ : Fin r := ⟨1, hr1⟩
  have he : e₁ ≠ e₂ := fun h => by simp [e₁, e₂, Fin.ext_iff] at h
  obtain ⟨p, hp⟩ := L.hit_mem e₁ j
  obtain ⟨q, hq⟩ := L.hit_mem e₂ j
  obtain ⟨x₀, hx₀, hx₀'⟩ := L.exists_start he ⟨_, L.hit_le e₁ j, hp.symm⟩
    ⟨_, L.hit_le e₂ j, hq.symm⟩
  -- The first offset `m i` from `x₀` of `P_i` on `C_j`.
  have hexm : ∀ i : Fin r, ∃ y, y < L.n j ∧ L.OnSpoke i (L.c j (x₀ + y)) := by
    intro i
    obtain ⟨x, hx⟩ := L.hit_mem i j
    obtain ⟨y, hy, hyx⟩ := L.exists_offset j x₀ x
    exact ⟨y, hy, ⟨_, L.hit_le i j, by rw [hyx, hx]⟩⟩
  let m : Fin r → ℕ := fun i => Nat.find (hexm i)
  have hm_lt : ∀ i, m i < L.n j := fun i => (Nat.find_spec (hexm i)).1
  have hm_on : ∀ i, L.OnSpoke i (L.c j (x₀ + m i)) := fun i => (Nat.find_spec (hexm i)).2
  have hm_min : ∀ i y, y < L.n j → L.OnSpoke i (L.c j (x₀ + y)) → m i ≤ y :=
    fun i y hy h => Nat.find_min' (hexm i) ⟨hy, h⟩
  have hm_inj : Function.Injective m := fun i i' h => (hm_on i).eq (h ▸ hm_on i')
  set e₀ : Fin r := e₁
  have hm₀ : m e₀ = 0 := Nat.le_zero.mp (hm_min e₀ 0 hn (by simpa using hx₀))
  set σ := Tuple.sort m
  have hσ : StrictMono (m ∘ σ) :=
    (Tuple.monotone_sort m).strictMono_of_injective (hm_inj.comp σ.injective)
  have hσ0 : σ ⟨0, hr⟩ = e₀ := by
    have h1 : m (σ ⟨0, hr⟩) ≤ m (σ (σ.symm e₀)) := hσ.monotone (Fin.le_def.mpr (Nat.zero_le _))
    rw [Equiv.apply_symm_apply, hm₀] at h1
    exact hm_inj (by omega)
  -- The positions from `m (σ k)` up to before `m (σ (k + 1))` are owned by `P_{σ k}`.
  have hrun : ∀ (k : Fin r) (t y : ℕ), y = m (σ k) + t → y < L.n j →
      (∀ k', k < k' → y < m (σ k')) → L.owner j (x₀ + y) = some (σ k) := by
    intro k t
    induction t with
    | zero =>
      intro y hy _ _
      subst hy
      exact owner_of_onSpoke hr (hm_on _)
    | succ t ih =>
      intro y hy hyn hlt
      have ih' := ih (m (σ k) + t) rfl (by omega) fun k' hk' => by have := hlt k' hk'; omega
      by_cases hmk : L.c j (x₀ + y) ∈ L.marked
      · obtain ⟨e, he⟩ := hmk
        obtain ⟨k'', rfl⟩ := σ.surjective e
        have hle : m (σ k'') ≤ y := hm_min _ y hyn he
        rcases lt_trichotomy k'' k with hlt' | rfl | hgt
        · exfalso
          have hmlt : m (σ k'') < m (σ k) := hσ hlt'
          by_cases he₀ : σ k'' = e₀
          · -- `P_{e₀}` would leave and come back before position `n j - 1`.
            have hne' : y ≠ L.n j - 1 := by
              intro h
              apply hx₀'
              rw [show x₀ + L.n j - 1 = x₀ + y by omega, ← he₀]
              exact he
            have hzk : ∀ k' ≤ L.len (σ k''), L.d (σ k'') k' ≠ L.c j (x₀ + m (σ k)) := by
              intro k' hk' h
              exact (show σ k'' ≠ σ k from fun h' => hlt'.ne (σ.injective h'))
                (OnSpoke.eq ⟨k', hk', h⟩ (hm_on (σ k)))
            have hyk : ∀ k' ≤ L.len (σ k''), L.d (σ k'') k' ≠ L.c j (x₀ + L.n j - 1) := by
              intro k' hk' h
              rw [he₀] at h hk'
              exact hx₀' ⟨k', hk', h⟩
            obtain ⟨k₀, hk₀, hdk₀⟩ := hm_on e₀
            rw [hm₀] at hdk₀
            rw [← he₀] at hk₀ hdk₀
            obtain ⟨x'', hx1, hx2, hx3⟩ := L.arc (σ k'') j (x₀ + m (σ k)) (x₀ + L.n j - 1)
              (by omega) hzk hyk (x₀ + y) (by omega) (by omega) he (x₀ + 0) k₀ hk₀ hdk₀
            have := L.eq_of_c_eq_window (x₀ := x₀) (a := x'' - x₀) (b := 0) (by omega) hn
              (by rw [show x₀ + (x'' - x₀) = x'' by omega]; exact hx3)
            omega
          · -- `P_{σ k''}` would leave and come back inside the window.
            have hpos : 0 < m (σ k'') := by
              rcases Nat.eq_zero_or_pos (m (σ k'')) with h0 | h0
              · exact absurd ((hm_on (σ k'')).eq (by rw [h0]; simpa using hx₀)) he₀
              · exact h0
            have hzk : ∀ k' ≤ L.len (σ k''), L.d (σ k'') k' ≠ L.c j x₀ := by
              intro k' hk' h
              exact he₀ (OnSpoke.eq ⟨k', hk', h⟩ hx₀)
            have hyk : ∀ k' ≤ L.len (σ k''), L.d (σ k'') k' ≠ L.c j (x₀ + m (σ k)) := by
              intro k' hk' h
              exact (show σ k'' ≠ σ k from fun h' => hlt'.ne (σ.injective h'))
                (OnSpoke.eq ⟨k', hk', h⟩ (hm_on (σ k)))
            obtain ⟨k₁, hk₁, hdk₁⟩ := he
            obtain ⟨x'', hx1, hx2, hx3⟩ := L.arc (σ k'') j x₀ (x₀ + m (σ k)) (by omega) hzk hyk
              (x₀ + m (σ k'')) (by omega) (by omega) (hm_on _) (x₀ + y) k₁ hk₁ hdk₁
            have := L.eq_of_c_eq_window (x₀ := x₀) (a := x'' - x₀) (b := y) (by omega) hyn
              (by rw [show x₀ + (x'' - x₀) = x'' by omega]; exact hx3)
            omega
        · exact owner_of_onSpoke hr he
        · exact absurd (hlt k'' hgt) (by omega)
      · rw [show x₀ + y = x₀ + (m (σ k) + t) + 1 by omega, owner_succ hr (by
          rw [show x₀ + (m (σ k) + t) + 1 = x₀ + y by omega]; exact hmk)]
        exact ih'
  refine ⟨σ, fun k _ => ?_⟩
  by_cases hk : k.1 + 1 < r
  · have hnext : nextSpoke k = ⟨k.1 + 1, hk⟩ := Fin.ext (by simp [nextSpoke, Nat.mod_eq_of_lt hk])
    rw [hnext]
    have hlt : m (σ k) < m (σ ⟨k.1 + 1, hk⟩) := hσ (Fin.lt_def.mpr (by simp))
    refine ⟨x₀ + (m (σ ⟨k.1 + 1, hk⟩) - 1), Or.inl ⟨?_, ?_⟩⟩
    · refine hrun k (m (σ ⟨k.1 + 1, hk⟩) - 1 - m (σ k)) _ (by omega)
        (by have := hm_lt (σ ⟨k.1 + 1, hk⟩); omega) fun k' hk' => ?_
      have : m (σ ⟨k.1 + 1, hk⟩) ≤ m (σ k') :=
        hσ.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hk'; simp; omega))
      omega
    · rw [show x₀ + (m (σ ⟨k.1 + 1, hk⟩) - 1) + 1 = x₀ + m (σ ⟨k.1 + 1, hk⟩) by omega]
      exact owner_of_onSpoke hr (hm_on _)
  · have hk' : k.1 = r - 1 := by have := k.2; omega
    have hnext : nextSpoke k = ⟨0, hr⟩ := Fin.ext (by
      simp only [nextSpoke]
      rw [show k.1 + 1 = r by omega, Nat.mod_self])
    rw [hnext, hσ0]
    refine ⟨x₀ + (L.n j - 1), Or.inl ⟨?_, ?_⟩⟩
    · refine hrun k (L.n j - 1 - m (σ k)) _ (by have := hm_lt (σ k); omega) (by omega)
        fun k' hk'' => absurd hk'' (by have := k'.2; rw [Fin.lt_def]; omega)
    · rw [show x₀ + (L.n j - 1) + 1 = x₀ + L.n j by omega]
      rw [owner_eq_of_c_eq hr (L.c_add j x₀)]
      exact owner_of_onSpoke hr hx₀


/-! ## The branch sets -/

variable (L) in
/-- The part of `P_i` from its first vertex on `C_j` up to just before `C_{j + 1}`. -/
@[expose] def seg (i : Fin r) (j : Fin s) : Set α :=
  {u | ∃ t, L.hit i j ≤ t ∧ t ≤ L.len i ∧ (∀ j', j < j' → t < L.hit i j') ∧ L.d i t = u}

variable (L) in
/-- The vertices of `C_j` at positions owned by `P_i`. -/
@[expose] def own (i : Fin r) (j : Fin s) : Set α :=
  {u | ∃ x, L.owner j x = some i ∧ L.c j x = u}

variable (L) in
/-- The branch set of the cylinder vertex `(k, j)`, where `σ k` is the radial path of the radial
line `k`. -/
@[expose] def branch (σ : Equiv.Perm (Fin r)) (p : Fin r × Fin s) : Set α :=
  L.seg (σ p.1) p.2 ∪ L.own (σ p.1) p.2

omit hr in
/-- A vertex of `P_i` on `C_j` is in the part of `P_i` for `C_j`. -/
theorem mem_seg_of_eq {i : Fin r} {j : Fin s} {t x : ℕ} (ht : t ≤ L.len i)
    (h : L.d i t = L.c j x) : L.d i t ∈ L.seg i j := by
  refine ⟨t, ?_, ht, fun j' hj' => L.level i j j' t x ht h hj', rfl⟩
  by_contra hlt
  push Not at hlt
  exact L.hit_min i j t hlt x h.symm

omit hr in
/-- A vertex of `P_i` on `C_j` comes after the first one and before `P_i` reaches a later circuit. -/
theorem level_of_eq {i : Fin r} {j : Fin s} {t x : ℕ} (ht : t ≤ L.len i)
    (h : L.d i t = L.c j x) : L.hit i j ≤ t ∧ ∀ j', j < j' → t < L.hit i j' := by
  obtain ⟨t', h1, h2, h3, h4⟩ := mem_seg_of_eq ht h
  have := L.d_inj i t' t h2 ht h4
  subst this
  exact ⟨h1, h3⟩

omit hr in
theorem hub_mem_seg (i : Fin r) (j : Fin s) : L.d i (L.hit i j) ∈ L.seg i j := by
  obtain ⟨x, hx⟩ := L.hit_mem i j
  exact mem_seg_of_eq (L.hit_le i j) hx.symm

omit hr in
theorem seg_subset (i : Fin r) (j : Fin s) : L.seg i j ⊆ V(G) := by
  rintro _ ⟨t, -, ht, -, rfl⟩
  exact L.d_mem i t ht

omit hr in
theorem own_subset (i : Fin r) (j : Fin s) : L.own i j ⊆ V(G) := by
  rintro _ ⟨x, -, rfl⟩
  exact L.c_mem j x

/-- The branch set of `P_i` and `C_j` is connected: each of its vertices is joined to the first
vertex of `P_i` on `C_j`, along `P_i` or along `C_j` and then along `P_i`. -/
theorem isGraphConnected_seg_own (i : Fin r) (j : Fin s) :
    IsGraphConnected (G.induce (L.seg i j ∪ L.own i j)) := by
  set Z := L.seg i j ∪ L.own i j with hZ
  set h₀ := L.d i (L.hit i j)
  have hh₀ : h₀ ∈ Z := Or.inl (hub_mem_seg i j)
  -- Walks along `P_i`.
  have hseg : ∀ u ∈ L.seg i j, Nonempty (GraphWalk (G.induce Z) h₀ u) := by
    rintro _ ⟨t, hht, ht, hlev, rfl⟩
    have hW := seqWalk (G := G.induce Z) (L.d i) (L.δ i) (L.hit i j) hh₀ (t - L.hit i j)
      (fun k hk => ⟨L.d_link i _ (by omega),
        Or.inl ⟨_, by omega, by omega, fun j' hj' => by have := hlev j' hj'; omega, rfl⟩,
        Or.inl ⟨_, by omega, by omega, fun j' hj' => by have := hlev j' hj'; omega, rfl⟩⟩)
    rw [show L.hit i j + (t - L.hit i j) = t by omega] at hW
    exact ⟨hW⟩
  -- Walks along `C_j` back to the last vertex of `P_i`.
  have hown : ∀ u ∈ L.own i j, Nonempty (GraphWalk (G.induce Z) h₀ u) := by
    rintro _ ⟨x, hox, rfl⟩
    have hK := L.exists_marked hr j
    obtain ⟨hlt, hmem, -⟩ := backIdx_spec (L.n_pos j) (L.c_mod j) hK x
    set b := backIdx (L.n j) (L.c j) L.marked x with hb
    have hrun := fun k (hk : k ≤ b) =>
      ownerIdx_run (L.n_pos j) (L.c_mod j) hK L.lab x hk
    -- The positions of the run are owned by `P_i`.
    have hrunZ : ∀ k ≤ b, L.c j (x + L.n j - b + k) ∈ Z := fun k hk =>
      Or.inr ⟨_, by rw [← hox]; exact (hrun k hk).1, rfl⟩
    -- The start of the run is on `P_i`.
    obtain ⟨i', hi'⟩ := hmem
    have hii' : i' = i := by
      have h1 := owner_of_onSpoke hr hi'
      have h2 : L.owner j (x + L.n j - b) = L.owner j x := by
        have := (hrun 0 (Nat.zero_le _)).1
        rwa [Nat.add_zero] at this
      rw [h2, hox] at h1
      exact (Option.some.inj h1).symm
    subst hii'
    obtain ⟨t, ht, hdt⟩ := hi'
    obtain ⟨W₁⟩ := hseg _ (mem_seg_of_eq ht hdt)
    have hW₂ := seqWalk (G := G.induce Z) (L.c j) (L.ε j) (x + L.n j - b)
      (by simpa using hrunZ 0 (Nat.zero_le _)) b
      (fun k hk => ⟨L.c_link j _, hrunZ k hk.le, hrunZ (k + 1) hk⟩)
    rw [show x + L.n j - b + b = x + L.n j by omega, L.c_add] at hW₂
    rw [hdt] at W₁
    exact ⟨W₁.append hW₂⟩
  refine ⟨⟨h₀, hh₀⟩, fun u hu w hw => ?_⟩
  have hwalk : ∀ u ∈ Z, Nonempty (GraphWalk (G.induce Z) h₀ u) := fun u hu =>
    hu.elim (hseg u) (hown u)
  obtain ⟨W₁⟩ := hwalk u hu
  obtain ⟨W₂⟩ := hwalk w hw
  exact ⟨W₁.reverse.append W₂⟩

/-- The branch sets of distinct cylinder vertices are disjoint. -/
theorem disjoint_branch (σ : Equiv.Perm (Fin r)) {p q : Fin r × Fin s} (hpq : p ≠ q) :
    Disjoint (L.branch σ p) (L.branch σ q) := by
  obtain ⟨k, j⟩ := p
  obtain ⟨k', j'⟩ := q
  -- A vertex of `P_i` in the part for `C_j` and on `C_{j'}` has `j = j'`.
  have hlev : ∀ {i : Fin r} {j j' : Fin s} {t x : ℕ}, L.d i t ∈ L.seg i j → t ≤ L.len i →
      L.d i t = L.c j' x → j = j' := by
    intro i j j' t x hseg ht hx
    obtain ⟨t', h1, h2, h3, h4⟩ := hseg
    have := L.d_inj i t' t h2 ht h4
    subst this
    obtain ⟨h1', h3'⟩ := level_of_eq ht hx
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd (h3 j' h) (by omega)
    · exact h
    · exact absurd (h3' j h) (by omega)
  refine Set.disjoint_left.mpr fun u hu hu' => hpq ?_
  simp only [branch] at hu hu'
  rcases hu with ⟨t, ht1, ht2, ht3, rfl⟩ | ⟨x, hx, rfl⟩ <;>
    rcases hu' with ⟨t', ht1', ht2', ht3', he⟩ | ⟨x', hx', he⟩
  · -- Both on radial paths.
    have hii : σ k = σ k' := by
      by_contra hne
      exact L.d_disj _ _ _ _ hne ht2 ht2' he.symm
    have hkk : k = k' := σ.injective hii
    subst hkk
    have htt := L.d_inj _ _ _ ht2' ht2 he
    subst htt
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd (ht3 j' h) (by omega)
    · rw [h]
    · exact absurd (ht3' j h) (by omega)
  · -- On `P_{σ k}` and owned on `C_{j'}`.
    have hon : L.OnSpoke (σ k) (L.c j' x') := ⟨t, ht2, he.symm⟩
    rw [owner_of_onSpoke hr hon] at hx'
    have hkk : k = k' := σ.injective (Option.some.inj hx')
    have hjj := hlev ⟨t, ht1, ht2, ht3, rfl⟩ ht2 he.symm
    rw [hkk, hjj]
  · -- Owned on `C_j` and on `P_{σ k'}`.
    have hon : L.OnSpoke (σ k') (L.c j x) := ⟨t', ht2', he⟩
    rw [owner_of_onSpoke hr hon] at hx
    have hkk : k = k' := σ.injective (Option.some.inj hx).symm
    have hjj := hlev ⟨t', ht1', ht2', ht3', rfl⟩ ht2' he
    rw [hkk, hjj]
  · -- Both owned.
    have hjj : j = j' := by
      by_contra hne
      exact L.c_disj _ _ _ _ hne he.symm
    subst hjj
    rw [owner_eq_of_c_eq hr he.symm, hx'] at hx
    rw [σ.injective (Option.some.inj hx)]


omit hr in
/-- If the radial paths are consecutive on the first circuit as `σ` lists them, and consecutive
radial paths on one circuit are consecutive on the next, then they are consecutive on every
circuit. -/
theorem adj_all (hs : 0 < s) {σ : Equiv.Perm (Fin r)}
    (h0 : ∀ k, σ k ≠ σ (nextSpoke k) → L.Adj ⟨0, hs⟩ (σ k) (σ (nextSpoke k)))
    (hadj : ∀ (j : Fin s) (hj : j.1 + 1 < s) (a b : Fin r), a ≠ b → L.Adj j a b →
      L.Adj ⟨j.1 + 1, hj⟩ a b)
    (j : Fin s) (k : Fin r) (hk : σ k ≠ σ (nextSpoke k)) : L.Adj j (σ k) (σ (nextSpoke k)) := by
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => exact h0 k hk
  | succ m ih => exact hadj ⟨m, by omega⟩ hm _ _ hk (ih (by omega))

omit hr in
/-- Every edge of the cylinder between distinct vertices comes from an edge of `G` between their
branch sets: an edge of a radial path for a radial edge, and an edge of a circuit where the owner
changes for a circular edge. -/
theorem branch_edge {σ : Equiv.Perm (Fin r)}
    (hR : ∀ j k, σ k ≠ σ (nextSpoke k) → L.Adj j (σ k) (σ (nextSpoke k))) :
    ∀ e p q, (cylinderGraph r s).IsLink e p q → p ≠ q →
      ∃ x ∈ L.branch σ p, ∃ y ∈ L.branch σ q, ∃ f, G.IsLink f x y := by
  -- The circular edges.
  have hcirc : ∀ (k : Fin r) (j : Fin s), k ≠ nextSpoke k →
      ∃ x ∈ L.branch σ (k, j), ∃ y ∈ L.branch σ (nextSpoke k, j), ∃ f, G.IsLink f x y := by
    intro k j hk
    obtain ⟨x, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hR j k (fun h => hk (σ.injective h))
    · exact ⟨L.c j x, Or.inr ⟨x, h1, rfl⟩, L.c j (x + 1), Or.inr ⟨x + 1, h2, rfl⟩, _,
        L.c_link j x⟩
    · exact ⟨L.c j (x + 1), Or.inr ⟨x + 1, h2, rfl⟩, L.c j x, Or.inr ⟨x, h1, rfl⟩, _,
        (L.c_link j x).symm⟩
  -- The radial edges.
  have hrad : ∀ (k : Fin r) (j : Fin s) (h : j.1 + 1 < s),
      ∃ x ∈ L.branch σ (k, j), ∃ y ∈ L.branch σ (k, ⟨j.1 + 1, h⟩), ∃ f, G.IsLink f x y := by
    intro k j h
    set i := σ k
    set j₁ : Fin s := ⟨j.1 + 1, h⟩
    obtain ⟨t₀, h01, h02, h03, h04⟩ := hub_mem_seg (L := L) i j
    have ht₀ := L.d_inj i _ _ h02 (L.hit_le i j) h04
    subst ht₀
    obtain ⟨t₁, h11, h12, h13, h14⟩ := hub_mem_seg (L := L) i j₁
    have ht₁ := L.d_inj i _ _ h12 (L.hit_le i j₁) h14
    subst ht₁
    have hlt : L.hit i j < L.hit i j₁ := h03 j₁ (Fin.lt_def.mpr (by simp [j₁]))
    refine ⟨L.d i (L.hit i j₁ - 1), ?_, L.d i (L.hit i j₁), Or.inl (hub_mem_seg i j₁),
      L.δ i (L.hit i j₁ - 1), ?_⟩
    · show _ ∈ L.seg i j ∪ L.own i j
      refine Or.inl ⟨_, by omega, by omega, fun j' hj' => ?_, rfl⟩
      rcases eq_or_lt_of_le (show j₁ ≤ j' from Fin.le_def.mpr (by
        have := Fin.lt_def.mp hj'; simp [j₁]; omega)) with h' | h'
      · subst h'
        omega
      · have := h13 j' h'
        omega
    · have := L.d_link i (L.hit i j₁ - 1) (by omega)
      rwa [show L.hit i j₁ - 1 + 1 = L.hit i j₁ by omega] at this
  intro e p q hl hpq
  cases e with
  | inl p₀ =>
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hcirc p₀.1 p₀.2 fun h => hpq (by rw [h1, h2]; exact Prod.ext h rfl)
    · rw [h1, h2]
      obtain ⟨x, hx, y, hy, f, hf⟩ :=
        hcirc p₀.1 p₀.2 fun h => hpq (by rw [h1, h2]; exact Prod.ext h.symm rfl)
      exact ⟨y, hy, x, hx, f, hf.symm⟩
  | inr p₀ =>
    obtain ⟨h, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hl
    · rw [h1, h2]
      exact hrad p₀.1 p₀.2 h
    · rw [h1, h2]
      obtain ⟨x, hx, y, hy, f, hf⟩ := hrad p₀.1 p₀.2 h
      exact ⟨y, hy, x, hx, f, hf.symm⟩

omit hr in
/-- **The contraction of a sleeve onto the cylinder** (Graph Minors VIII, (11.1), page 273). Let
`G` contain a sleeve given by sequences, and let `W` be a set of vertices of `G` that meets the
sleeve exactly in the ends `d i (len i)` of its radial paths. Suppose two radial paths consecutive
on one circuit are consecutive on the next. Then a tree-decomposition `(T, Y)` of `G` gives a
tree-decomposition `(T, X)` of the graph induced on `W`, of no larger width, with
`Y_t ∩ W ⊆ X_t` for every `t` and with all the ends `d i (len i)` in one bag. -/
theorem exists_decomposition [Fintype ι] {T : SimpleGraph ι} {Y : ι → Set α} (hVG : V(G).Finite)
    (hTD : IsTreeDecomposition G T Y) {W : Set α} (hW : W ⊆ V(G)) (hs : 0 < s)
    (hrs : r ≤ 2 * s)
    (hadj : ∀ (j : Fin s) (hj : j.1 + 1 < s) (a b : Fin r), a ≠ b → L.Adj j a b →
      L.Adj ⟨j.1 + 1, hj⟩ a b)
    (hvW : ∀ i, L.d i (L.len i) ∈ W) (hdW : ∀ i k, k < L.len i → L.d i k ∉ W)
    (hcW : ∀ j x, L.c j x ∉ W) :
    ∃ X : ι → Set α, IsTreeDecomposition (G.induce W) T X ∧
      (∀ w : ℕ, TreeDecompHasWidthLE Y w → TreeDecompHasWidthLE X w) ∧
      (∀ t, Y t ∩ W ⊆ X t) ∧ ∃ t₀, range (fun i => L.d i (L.len i)) ⊆ X t₀ := by
  classical
  by_cases hr : 0 < r
  swap
  · -- No radial paths: the cylinder has no vertices.
    have hr0 : r = 0 := by omega
    subst hr0
    obtain ⟨X, hX, hXw, hXY, t₀, -⟩ := exists_decomposition_of_cylinder_model hVG hTD hW hs hrs
      (fun _ => (∅ : Set α)) (fun p => p.1.elim0) (fun p => p.1.elim0) (fun p => p.1.elim0)
      (fun i : Fin 0 => L.d i (L.len i)) (fun i => i.elim0) (fun i => i.elim0)
      (fun p => p.1.elim0) (fun _ p => p.1.elim0)
    exact ⟨X, hX, hXw, hXY, t₀, by rintro _ ⟨i, -⟩; exact i.elim0⟩
  obtain ⟨σ, hσ⟩ := L.exists_order hr ⟨0, hs⟩
  have hR := L.adj_all hs hσ hadj
  set last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  obtain ⟨X, hX, hXw, hXY, t₀, hX₀⟩ := exists_decomposition_of_cylinder_model hVG hTD hW hs hrs
    (L.branch σ) (fun p => union_subset (seg_subset _ _) (own_subset _ _))
    (fun p => isGraphConnected_seg_own hr _ _) (fun p q hpq => disjoint_branch hr σ hpq)
    (fun k => L.d (σ k) (L.len (σ k)))
    (fun k => Or.inl ⟨_, L.hit_le _ _, le_rfl, fun j' hj' => by
      have := Fin.lt_def.mp hj'; have := j'.2; simp at *; omega, rfl⟩)
    (fun k => hvW (σ k))
    (fun p u hu huW => by
      rcases hu with ⟨t, ht1, ht2, ht3, rfl⟩ | ⟨x, -, rfl⟩
      · have htl : t = L.len (σ p.1) := by
          by_contra hne
          exact hdW _ t (by omega) huW
        subst htl
        refine ⟨?_, rfl⟩
        by_contra hj
        have := ht3 last (Fin.lt_def.mpr (by have := p.2.2; simp [last]; omega))
        have := L.hit_le (σ p.1) last
        omega
      · exact absurd huW (hcW _ _))
    (L.branch_edge hR)
  refine ⟨X, hX, hXw, hXY, t₀, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hX₀ ⟨σ.symm i, by simp⟩

end SleeveSeq

end GM08
end GraphMinor
