module

public import GraphMinor.GM11.Walks

/-!
# Paths and circuits as sequences, for the proof of Graph Minors VIII, (11.1)

To contract a sleeve onto the cylinder we walk along its circuits and its radial paths. Here a path
is a sequence `c 0, c 1, …, c ℓ` of vertices with an edge `ε k` from `c k` to `c (k + 1)`, and a
circuit is such a sequence that repeats with period `n` (`GraphWalk.exists_seq`). A stretch of a
sequence is again a walk (`seqWalk`).

Two tools are proved here.

* **Owners.** Some vertices of a circuit are *marked* (in the sleeve, the vertices on a radial
  path). The *owner* of a position `x` is the label of the last marked vertex at or before `x`
  (`ownerIdx`). Positions between two consecutive marked vertices have the owner of the first one.
* **Confinement.** A connected graph `Q` whose edges join consecutive positions, and which has a
  vertex strictly between two positions `z < y` but no vertex at `z` or `y`, has all its vertices
  strictly between `z` and `y` (`exists_pos_of_walk`). This is how we see that the intersection of a
  radial path with a circuit, which is a path, is an interval of both.
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph Surface

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ## Stretches of a sequence -/

/-- The walk `c p, c (p + 1), …, c (p + ℓ)` along the edges `ε p, …, ε (p + ℓ - 1)`. -/
@[expose] def seqWalk (c : ℕ → α) (ε : ℕ → β) (p : ℕ) (hp : c p ∈ V(G)) :
    (ℓ : ℕ) → (∀ k < ℓ, G.IsLink (ε (p + k)) (c (p + k)) (c (p + k + 1))) →
      GraphWalk G (c p) (c (p + ℓ))
  | 0, _ => .nil hp
  | ℓ + 1, h => (seqWalk c ε p hp ℓ fun k hk => h k (Nat.lt_succ_of_lt hk)).append
      (.cons (h ℓ (Nat.lt_succ_self ℓ)) (.nil (h ℓ (Nat.lt_succ_self ℓ)).right_mem))

variable {c : ℕ → α} {ε : ℕ → β} {p : ℕ} {hp : c p ∈ V(G)}

theorem mem_seqWalk_support {ℓ : ℕ} {h : ∀ k < ℓ, G.IsLink (ε (p + k)) (c (p + k)) (c (p + k + 1))}
    {x : α} : x ∈ (seqWalk c ε p hp ℓ h).support ↔ ∃ k ≤ ℓ, c (p + k) = x := by
  induction ℓ with
  | zero =>
    simp only [seqWalk, GraphWalk.support_nil, List.mem_singleton, Nat.le_zero, exists_eq_left,
      Nat.add_zero]
    exact eq_comm
  | succ ℓ ih =>
    rw [seqWalk, GraphWalk.mem_support_append, ih]
    simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl | rfl)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨ℓ, by omega, rfl⟩
      · exact ⟨ℓ + 1, le_rfl, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (ℓ + 1) with hk' | hk'
      · exact Or.inl ⟨k, by omega, rfl⟩
      · have : k = ℓ + 1 := by omega
        subst this
        exact Or.inr (Or.inr rfl)

theorem mem_seqWalk_edges {ℓ : ℕ} {h : ∀ k < ℓ, G.IsLink (ε (p + k)) (c (p + k)) (c (p + k + 1))}
    {e : β} : e ∈ (seqWalk c ε p hp ℓ h).edges ↔ ∃ k < ℓ, ε (p + k) = e := by
  induction ℓ with
  | zero => simp [seqWalk]
  | succ ℓ ih =>
    rw [seqWalk, GraphWalk.edges_append, List.mem_append, ih]
    simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨ℓ, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k ℓ with hk' | hk'
      · exact Or.inl ⟨k, hk', rfl⟩
      · have : k = ℓ := by omega
        subst this
        exact Or.inr rfl

/-- A walk is a sequence of vertices and edges. -/
theorem GraphWalk.exists_seq [Nonempty β] {u w : α} (W : GraphWalk G u w) :
    ∃ (c : ℕ → α) (ε : ℕ → β), c 0 = u ∧ c W.length = w ∧
      (∀ k < W.length, G.IsLink (ε k) (c k) (c (k + 1))) ∧
      (∀ x, x ∈ W.support ↔ ∃ k ≤ W.length, c k = x) ∧
      (∀ e, e ∈ W.edges ↔ ∃ k < W.length, ε k = e) ∧
      (W.support.tail.Nodup → ∀ k k', 0 < k → 0 < k' → k ≤ W.length → k' ≤ W.length →
        c k = c k' → k = k') ∧
      (W.support.Nodup → ∀ k k', k ≤ W.length → k' ≤ W.length → c k = c k' → k = k') ∧
      (W.edges.Nodup → ∀ k k', k < W.length → k' < W.length → ε k = ε k' → k = k') := by
  induction W with
  | @nil a ha =>
    refine ⟨fun _ => a, fun _ => Classical.arbitrary β, rfl, rfl, fun k hk => by simp at hk,
      fun x => ?_, fun e => by simp, fun _ k k' hk _ hk' _ _ => by simp at hk'; omega,
      fun _ k k' hk hk' _ => by simp at hk hk'; omega, fun _ k _ hk => by simp at hk⟩
    simp only [GraphWalk.support_nil, List.mem_singleton, GraphWalk.length_nil, Nat.le_zero,
      exists_eq_left]
    exact eq_comm
  | @cons a b w' e hl r ih =>
    obtain ⟨c, ε, hc0, hcl, hlink, hsupp, hedges, htail, hnd, hend⟩ := ih
    refine ⟨fun k => match k with | 0 => a | k + 1 => c k,
      fun k => match k with | 0 => e | k + 1 => ε k, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hcl
    · intro k hk
      rcases k with _ | k
      · simpa [hc0] using hl
      · simp only [GraphWalk.length_cons] at hk
        exact hlink k (by omega)
    · intro x
      simp only [GraphWalk.support_cons, List.mem_cons, hsupp, GraphWalk.length_cons]
      constructor
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨k + 1, by omega, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        rcases k with _ | k
        · exact Or.inl rfl
        · exact Or.inr ⟨k, by omega, rfl⟩
    · intro f
      simp only [GraphWalk.edges_cons, List.mem_cons, hedges, GraphWalk.length_cons]
      constructor
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨k + 1, by omega, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        rcases k with _ | k
        · exact Or.inl rfl
        · exact Or.inr ⟨k, by omega, rfl⟩
    · intro hT k k' hk hk' hkl hkl' hkk
      simp only [GraphWalk.support_cons, List.tail_cons, GraphWalk.length_cons] at hT hkl hkl'
      rcases k with _ | k
      · omega
      rcases k' with _ | k'
      · omega
      exact congrArg (· + 1) (hnd hT k k' (by omega) (by omega) hkk)
    · intro hN k k' hkl hkl' hkk
      simp only [GraphWalk.support_cons, List.nodup_cons, GraphWalk.length_cons] at hN hkl hkl'
      rcases k with _ | k <;> rcases k' with _ | k'
      · rfl
      · exact absurd ((hsupp _).mpr ⟨k', by omega, hkk.symm⟩) hN.1
      · exact absurd ((hsupp _).mpr ⟨k, by omega, hkk⟩) hN.1
      · exact congrArg (· + 1) (hnd hN.2 k k' (by omega) (by omega) hkk)
    · intro hN k k' hkl hkl' hkk
      simp only [GraphWalk.edges_cons, List.nodup_cons, GraphWalk.length_cons] at hN hkl hkl'
      rcases k with _ | k <;> rcases k' with _ | k'
      · rfl
      · exact absurd ((hedges _).mpr ⟨k', by omega, hkk.symm⟩) hN.1
      · exact absurd ((hedges _).mpr ⟨k, by omega, hkk⟩) hN.1
      · exact congrArg (· + 1) (hend hN.2 k k' (by omega) (by omega) hkk)

/-! ## Confinement -/

/-- A walk of a graph `Q` whose edges move one step along a sequence of positions, starting
strictly between two positions `z < y` that carry no vertex of `Q`, ends strictly between them.
Here `At x a` says that position `x` carries the vertex `a`. -/
theorem exists_pos_of_walk {Q : Graph α β} (At : ℕ → α → Prop)
    (hstep : ∀ e a a' x, Q.IsLink e a a' → At x a → At (x + 1) a' ∨ (0 < x ∧ At (x - 1) a'))
    {z y : ℕ} (hz : ∀ a ∈ V(Q), ¬ At z a) (hy : ∀ a ∈ V(Q), ¬ At y a) {a b : α}
    (W : GraphWalk Q a b) {x : ℕ} (hzx : z < x) (hxy : x < y) (hx : At x a) :
    ∃ x', z < x' ∧ x' < y ∧ At x' b := by
  induction W generalizing x with
  | nil _ => exact ⟨x, hzx, hxy, hx⟩
  | cons hl r ih =>
    rcases hstep _ _ _ x hl hx with h | ⟨hx0, h⟩
    · have hne : x + 1 ≠ y := fun he => hy _ hl.right_mem (he ▸ h)
      exact ih (by omega) (by omega) h
    · have hne : x - 1 ≠ z := fun he => hz _ hl.right_mem (he ▸ h)
      exact ih (by omega) (by omega) h

/-! ## Owners of the positions of a circuit -/

section Owner

variable (n : ℕ) (c : ℕ → α) (K : Set α)

/-- The distance back from position `x` to the last marked position at or before `x`. Marked
positions are those carrying a vertex of `K`; `c` has period `n`. -/
@[expose] noncomputable def backIdx (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, t < n ∧ c (x + n - t) ∈ K then Nat.find h else 0

/-- The owner of position `x`: the label of the last marked vertex at or before `x`. -/
@[expose] noncomputable def ownerIdx {γ : Type*} (lab : α → γ) (x : ℕ) : γ :=
  lab (c (x + n - backIdx n c K x))

variable {n c K}

/-- Shifting a position by a multiple of the period does not change its vertex. -/
theorem seq_mod_eq (hper : ∀ x, c (x % n) = c x) {x y : ℕ} (h : x % n = y % n) : c x = c y := by
  rw [← hper x, h, hper]

theorem seq_add_period (hper : ∀ x, c (x % n) = c x) (x : ℕ) : c (x + n) = c x :=
  seq_mod_eq hper (Nat.add_mod_right x n)

/-- Two positions with the same vertex are equal modulo the period. -/
theorem seq_mod_eq_of_eq (hn : 0 < n) (hper : ∀ x, c (x % n) = c x)
    (hinj : ∀ x y, x < n → y < n → c x = c y → x = y) {x y : ℕ} (h : c x = c y) :
    x % n = y % n :=
  hinj _ _ (Nat.mod_lt x hn) (Nat.mod_lt y hn) (by rw [hper, hper, h])

variable (hn : 0 < n) (hper : ∀ x, c (x % n) = c x) (hK : ∃ x, c x ∈ K)
include hn hper hK

theorem exists_back (x : ℕ) : ∃ t, t < n ∧ c (x + n - t) ∈ K := by
  obtain ⟨q, hq⟩ := hK
  set m := x + n - q % n with hm
  have hqn := Nat.mod_lt q hn
  refine ⟨m % n, Nat.mod_lt m hn, ?_⟩
  have hdiv := Nat.mod_add_div m n
  have heq : x + n - m % n = q % n + n * (m / n) := by omega
  rw [heq, ← seq_mod_eq hper (show q % n % n = (q % n + n * (m / n)) % n by
    rw [Nat.add_mul_mod_self_left])]
  rw [hper]
  exact hq

theorem backIdx_spec (x : ℕ) :
    backIdx n c K x < n ∧ c (x + n - backIdx n c K x) ∈ K ∧
      ∀ t < backIdx n c K x, c (x + n - t) ∉ K := by
  classical
  have h := exists_back hn hper hK x
  have hb : backIdx n c K x = Nat.find h := by simp only [backIdx]; rw [dite_eq_left h]
  rw [hb]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun t ht hc => ?_⟩
  have := Nat.find_min h ht
  exact this ⟨ht.trans (Nat.find_spec h).1, hc⟩

theorem backIdx_eq_zero {x : ℕ} (hx : c x ∈ K) : backIdx n c K x = 0 := by
  classical
  have h := exists_back hn hper hK x
  have hb : backIdx n c K x = Nat.find h := by simp only [backIdx]; rw [dite_eq_left h]
  rw [hb, Nat.find_eq_zero]
  refine ⟨hn, ?_⟩
  rw [Nat.sub_zero, seq_add_period hper]
  exact hx

theorem backIdx_succ {x : ℕ} (hx : c (x + 1) ∉ K) :
    backIdx n c K (x + 1) = backIdx n c K x + 1 := by
  obtain ⟨hlt, hmem, hmin⟩ := backIdx_spec hn hper hK x
  obtain ⟨hlt', hmem', hmin'⟩ := backIdx_spec hn hper hK (x + 1)
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push Not at hgt
    exact hmin' (backIdx n c K x + 1) hgt (by
      rw [show x + 1 + n - (backIdx n c K x + 1) = x + n - backIdx n c K x by omega]
      exact hmem)
  · by_contra hgt
    push Not at hgt
    rcases Nat.eq_zero_or_pos (backIdx n c K (x + 1)) with h0 | hpos
    · rw [h0, Nat.sub_zero, seq_add_period hper] at hmem'
      exact hx hmem'
    · exact hmin (backIdx n c K (x + 1) - 1) (by omega) (by
        rw [show x + n - (backIdx n c K (x + 1) - 1) = x + 1 + n - backIdx n c K (x + 1) by omega]
        exact hmem')

theorem backIdx_mod {x y : ℕ} (h : x % n = y % n) : backIdx n c K x = backIdx n c K y := by
  -- The positions `x + n - t` and `y + n - t` carry the same vertex for `t < n`.
  have key : ∀ x y, x % n = y % n → backIdx n c K x ≤ backIdx n c K y := by
    intro x y h
    obtain ⟨hlt, hmem, -⟩ := backIdx_spec hn hper hK y
    obtain ⟨-, -, hmin⟩ := backIdx_spec hn hper hK x
    by_contra hgt
    push Not at hgt
    refine hmin _ hgt ?_
    rw [seq_mod_eq hper (show (x + n - backIdx n c K y) % n = (y + n - backIdx n c K y) % n by
      have hx := Nat.mod_add_div x n
      have hy := Nat.mod_add_div y n
      rw [show x + n - backIdx n c K y = (x % n + n - backIdx n c K y) + n * (x / n) by omega,
        show y + n - backIdx n c K y = (y % n + n - backIdx n c K y) + n * (y / n) by omega,
        Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, h])]
    exact hmem
  exact le_antisymm (key x y h) (key y x h.symm)

variable {γ : Type*} (lab : α → γ)

theorem ownerIdx_of_mem {x : ℕ} (hx : c x ∈ K) : ownerIdx n c K lab x = lab (c x) := by
  rw [ownerIdx, backIdx_eq_zero hn hper hK hx, Nat.sub_zero, seq_add_period hper]

theorem ownerIdx_succ {x : ℕ} (hx : c (x + 1) ∉ K) :
    ownerIdx n c K lab (x + 1) = ownerIdx n c K lab x := by
  rw [ownerIdx, ownerIdx, backIdx_succ hn hper hK hx]
  obtain ⟨hlt, -, -⟩ := backIdx_spec hn hper hK x
  rw [show x + 1 + n - (backIdx n c K x + 1) = x + n - backIdx n c K x by omega]

theorem ownerIdx_mod {x y : ℕ} (h : x % n = y % n) :
    ownerIdx n c K lab x = ownerIdx n c K lab y := by
  rw [ownerIdx, ownerIdx, backIdx_mod hn hper hK h]
  obtain ⟨hlt, -, -⟩ := backIdx_spec hn hper hK y
  congr 1
  refine seq_mod_eq hper ?_
  have hx := Nat.mod_add_div x n
  have hy := Nat.mod_add_div y n
  rw [show x + n - backIdx n c K y = (x % n + n - backIdx n c K y) + n * (x / n) by omega,
    show y + n - backIdx n c K y = (y % n + n - backIdx n c K y) + n * (y / n) by omega,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, h]

theorem ownerIdx_add_period (x : ℕ) : ownerIdx n c K lab (x + n) = ownerIdx n c K lab x :=
  ownerIdx_mod hn hper hK lab (Nat.add_mod_right x n)

/-- If the owner changes from `x` to `x + 1`, then `x + 1` is marked. -/
theorem mem_of_ownerIdx_ne {x : ℕ} (h : ownerIdx n c K lab x ≠ ownerIdx n c K lab (x + 1)) :
    c (x + 1) ∈ K := by
  by_contra hx
  exact h (ownerIdx_succ hn hper hK lab hx).symm

/-- The positions from the last marked position `x + n - backIdx x` up to `x` all have the owner
of `x`, and the ones after the marked one are not marked. -/
theorem ownerIdx_run (x : ℕ) {k : ℕ} (hk : k ≤ backIdx n c K x) :
    ownerIdx n c K lab (x + n - backIdx n c K x + k) = ownerIdx n c K lab x ∧
      (0 < k → c (x + n - backIdx n c K x + k) ∉ K) := by
  obtain ⟨hlt, hmem, hmin⟩ := backIdx_spec hn hper hK x
  have hnot : ∀ k, 0 < k → k ≤ backIdx n c K x → c (x + n - backIdx n c K x + k) ∉ K := by
    intro k hk0 hk
    have := hmin (backIdx n c K x - k) (by omega)
    rwa [show x + n - (backIdx n c K x - k) = x + n - backIdx n c K x + k by omega] at this
  refine ⟨?_, fun hk0 => hnot k hk0 hk⟩
  induction k with
  | zero =>
    rw [Nat.add_zero, ownerIdx_of_mem hn hper hK lab hmem]
    rw [ownerIdx, show x + n - backIdx n c K x = x + n - backIdx n c K x from rfl]
  | succ k ih =>
    have h := hnot (k + 1) (by omega) hk
    rw [← add_assoc] at h ⊢
    rw [ownerIdx_succ hn hper hK lab h]
    exact ih (by omega)

end Owner

end GM08
end GraphMinor
