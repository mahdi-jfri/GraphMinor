module

public import GraphMinor.Compute.Algorithm77Step73
public import GraphMinor.GM13.Section7Six

/-!
# Graph Minors XIII, (7.6): Computable Moving of Stars to External Stars on a Subwall

This file implements Step (7.6) (GM XIII, page 92) for the algorithm of (7.7):
given `k = p.choose 2` `(l, m + 4 * k)`-stars (`m ≥ 3`) with centers `v_0, ..., v_{k-1}` over a wall
`W : WallOfHeight h G`, we perform `k` applications of (7.3) with `r = 0`, at step `i` computing:
1. the subwall `H_i = H_{i-1}.step73Subwall ... v_i` of height `h - 2 * i` avoiding `v_i`, with
   brick distance `d_i ≥ d_{i-1} - 4`, and
2. Claim (1) of (7.6): for each star `a` and ray `j`, extending the ray by a minimal path `Q` in
   `H_{i-1}` from its endpoint `u` to `V(H_i)` via `extendStarRay`.

After `k` steps, all centers `v_0, ..., v_{k-1}` are outside `V(H_k)`, so the `k` extended
pre-stars over `H_k` are external `(l, m)`-stars (`H_k.IsStarRay`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

/-! ### Section 1: Canonical Simple Paths in `elementaryWall h` -/

/-- Horizontal path in row `y` moving right `d` steps from `(x, y)` to `(x + d, y)`. -/
def rowPathUp : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | x, 0, y => [(x, y)]
  | x, d + 1, y => (x, y) :: rowPathUp (x + 1) d y

theorem rowPathUp_ne_nil (x d y : ℕ) : rowPathUp x d y ≠ [] := by
  cases d <;> simp [rowPathUp]

theorem head_rowPathUp (x d y : ℕ) :
    (rowPathUp x d y).head (rowPathUp_ne_nil x d y) = (x, y) := by
  cases d <;> rfl

theorem getLast_rowPathUp : ∀ (x d y : ℕ),
    (rowPathUp x d y).getLast (rowPathUp_ne_nil x d y) = (x + d, y)
  | x, 0, y => by simp [rowPathUp]
  | x, d + 1, y => by
    have hne := rowPathUp_ne_nil (x + 1) d y
    calc (rowPathUp x (d + 1) y).getLast (rowPathUp_ne_nil x (d + 1) y)
        = (rowPathUp (x + 1) d y).getLast hne := List.getLast_cons hne
      _ = (x + 1 + d, y) := getLast_rowPathUp (x + 1) d y
      _ = (x + (d + 1), y) := by congr 1; omega

theorem mem_rowPathUp : ∀ {x d y : ℕ} {p : ℕ × ℕ},
    p ∈ rowPathUp x d y → x ≤ p.1 ∧ p.1 ≤ x + d ∧ p.2 = y
  | x, 0, y, p, hp => by
    simp only [rowPathUp, List.mem_singleton] at hp
    subst hp
    exact ⟨le_rfl, by omega, rfl⟩
  | x, d + 1, y, p, hp => by
    simp only [rowPathUp, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, by omega, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := mem_rowPathUp hp
      exact ⟨by omega, by omega, h3⟩

theorem nodup_rowPathUp : ∀ (x d y : ℕ), (rowPathUp x d y).Nodup
  | x, 0, y => List.nodup_singleton _
  | x, d + 1, y => by
    rw [rowPathUp, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_rowPathUp (x + 1) d y⟩
    have h1 := (mem_rowPathUp hmem).1
    dsimp at h1
    omega

theorem isChain_rowPathUp (h : ℕ) : ∀ (x d y : ℕ),
    (∀ i ≤ d, (x + i, y) ∈ GM13.elementaryWallVerts h) →
    List.IsChain (GM13.elementaryWallAdj h) (rowPathUp x d y)
  | x, 0, y, _ => List.isChain_singleton _
  | x, d + 1, y, hv => by
    have hadj : GM13.elementaryWallAdj h (x, y) (x + 1, y) :=
      ⟨by simpa using hv 0 (by omega), by simpa using hv 1 (by omega), Or.inl ⟨rfl, Or.inl rfl⟩⟩
    have ih := isChain_rowPathUp h (x + 1) d y (fun i hi => by
      have := hv (i + 1) (by omega)
      rwa [show x + (i + 1) = x + 1 + i by omega] at this)
    rw [rowPathUp, List.isChain_cons]
    refine ⟨?_, ih⟩
    intro q hq
    rw [List.head?_eq_some_head (rowPathUp_ne_nil (x + 1) d y), Option.mem_def,
      Option.some.injEq] at hq
    subst hq
    rw [head_rowPathUp]
    exact hadj

/-- Horizontal path in row `y` from `(x₁, y)` to `(x₂, y)`. -/
def rowPath (x₁ x₂ y : ℕ) : List (ℕ × ℕ) :=
  if x₁ ≤ x₂ then
    rowPathUp x₁ (x₂ - x₁) y
  else
    (rowPathUp x₂ (x₁ - x₂) y).reverse

theorem rowPath_ne_nil (x₁ x₂ y : ℕ) : rowPath x₁ x₂ y ≠ [] := by
  unfold rowPath
  split_ifs
  · exact rowPathUp_ne_nil _ _ _
  · exact List.reverse_ne_nil_iff.mpr (rowPathUp_ne_nil _ _ _)

theorem head_rowPath (x₁ x₂ y : ℕ) :
    (rowPath x₁ x₂ y).head (rowPath_ne_nil x₁ x₂ y) = (x₁, y) := by
  unfold rowPath
  split_ifs with hle
  · exact head_rowPathUp _ _ _
  · rw [List.head_reverse, getLast_rowPathUp]
    congr 1
    omega

theorem getLast_rowPath (x₁ x₂ y : ℕ) :
    (rowPath x₁ x₂ y).getLast (rowPath_ne_nil x₁ x₂ y) = (x₂, y) := by
  unfold rowPath
  split_ifs with hle
  · rw [getLast_rowPathUp]
    congr 1
    omega
  · rw [List.getLast_reverse, head_rowPathUp]

theorem snd_of_mem_rowPath {x₁ x₂ y : ℕ} {p : ℕ × ℕ} (hp : p ∈ rowPath x₁ x₂ y) :
    p.2 = y := by
  unfold rowPath at hp
  split_ifs at hp
  · exact (mem_rowPathUp hp).2.2
  · rw [List.mem_reverse] at hp
    exact (mem_rowPathUp hp).2.2

theorem nodup_rowPath (x₁ x₂ y : ℕ) : (rowPath x₁ x₂ y).Nodup := by
  unfold rowPath
  split_ifs
  · exact nodup_rowPathUp _ _ _
  · exact List.nodup_reverse.mpr (nodup_rowPathUp _ _ _)

theorem elementaryWallAdj_symm {h : ℕ} {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) :
    GM13.elementaryWallAdj h q p := by
  refine ⟨hpq.2.1, hpq.1, ?_⟩
  rcases hpq.2.2 with ⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr ⟨h2, h3⟩⟩
  · exact Or.inr ⟨h1.symm, Or.inl ⟨h2, h3⟩⟩

theorem isChain_rowPath {h x₁ x₂ y : ℕ}
    (hx₁ : (x₁, y) ∈ GM13.elementaryWallVerts h)
    (hx₂ : (x₂, y) ∈ GM13.elementaryWallVerts h) :
    List.IsChain (GM13.elementaryWallAdj h) (rowPath x₁ x₂ y) := by
  have hmid : ∀ i, min x₁ x₂ ≤ i → i ≤ max x₁ x₂ → (i, y) ∈ GM13.elementaryWallVerts h := by
    intro i h1 h2
    simp only [GM13.elementaryWallVerts, Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq] at hx₁ hx₂ ⊢
    omega
  unfold rowPath
  split_ifs with hle
  · exact isChain_rowPathUp h x₁ (x₂ - x₁) y (fun i hi => hmid (x₁ + i) (by omega) (by omega))
  · rw [List.isChain_reverse]
    have hc := isChain_rowPathUp h x₂ (x₁ - x₂) y (fun i hi => hmid (x₂ + i) (by omega) (by omega))
    exact hc.imp fun _ _ hadj => elementaryWallAdj_symm hadj

/-- Column `1` or `2` that has a vertical edge from `(vertCol y, y)` to `(vertCol y, y + 1)`. -/
def vertCol (y : ℕ) : ℕ :=
  if y % 2 = 0 then 1 else 2

theorem vertCol_mem_elementaryWallVerts {h y : ℕ} (hh : 1 ≤ h) (hy : y ≤ h) :
    (vertCol y, y) ∈ GM13.elementaryWallVerts h := by
  unfold vertCol
  split_ifs <;>
    (simp only [GM13.elementaryWallVerts, Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega)

theorem vertCol_mem_elementaryWallVerts_succ {h y : ℕ} (hh : 1 ≤ h) (hy : y + 1 ≤ h) :
    (vertCol y, y + 1) ∈ GM13.elementaryWallVerts h := by
  unfold vertCol
  split_ifs <;>
    (simp only [GM13.elementaryWallVerts, Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq]; omega)

theorem elementaryWallAdj_vertCol {h y : ℕ} (hh : 1 ≤ h) (hy : y + 1 ≤ h) :
    GM13.elementaryWallAdj h (vertCol y, y) (vertCol y, y + 1) := by
  refine ⟨vertCol_mem_elementaryWallVerts hh (by omega),
    vertCol_mem_elementaryWallVerts_succ hh hy, Or.inr ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩⟩
  unfold vertCol
  split_ifs with hev
  · exact ⟨y / 2, by omega⟩
  · exact ⟨y / 2 + 1, by omega⟩

/-- Canonical path in `elementaryWall h` moving up `d` rows from `(x₁, y₁)` to `(x₂, y₁ + d)`. -/
def elemWallUpPath (x₂ : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, x₁, y₁ => rowPath x₁ x₂ y₁
  | d + 1, x₁, y₁ =>
    rowPath x₁ (vertCol y₁) y₁ ++ elemWallUpPath x₂ d (vertCol y₁) (y₁ + 1)

theorem elemWallUpPath_ne_nil (x₂ d x₁ y₁ : ℕ) :
    elemWallUpPath x₂ d x₁ y₁ ≠ [] := by
  cases d with
  | zero => exact rowPath_ne_nil _ _ _
  | succ d =>
    simp [elemWallUpPath, rowPath_ne_nil]

theorem head_elemWallUpPath (x₂ d x₁ y₁ : ℕ) :
    (elemWallUpPath x₂ d x₁ y₁).head (elemWallUpPath_ne_nil x₂ d x₁ y₁) = (x₁, y₁) := by
  cases d with
  | zero => exact head_rowPath _ _ _
  | succ d =>
    simp only [elemWallUpPath, List.head_append_of_ne_nil (rowPath_ne_nil x₁ (vertCol y₁) y₁),
      head_rowPath]

theorem getLast_elemWallUpPath (x₂ : ℕ) : ∀ (d x₁ y₁ : ℕ),
    (elemWallUpPath x₂ d x₁ y₁).getLast (elemWallUpPath_ne_nil x₂ d x₁ y₁) = (x₂, y₁ + d)
  | 0, x₁, y₁ => by
    simpa [elemWallUpPath] using getLast_rowPath x₁ x₂ y₁
  | d + 1, x₁, y₁ => by
    simp only [elemWallUpPath,
      List.getLast_append_of_ne_nil _ (elemWallUpPath_ne_nil x₂ d (vertCol y₁) (y₁ + 1)),
      getLast_elemWallUpPath x₂ d (vertCol y₁) (y₁ + 1)]
    congr 1
    omega

theorem snd_of_mem_elemWallUpPath (x₂ : ℕ) : ∀ {d x₁ y₁ : ℕ} {p : ℕ × ℕ},
    p ∈ elemWallUpPath x₂ d x₁ y₁ → y₁ ≤ p.2 ∧ p.2 ≤ y₁ + d
  | 0, x₁, y₁, p, hp => by
    have hy := snd_of_mem_rowPath hp
    exact ⟨by omega, by omega⟩
  | d + 1, x₁, y₁, p, hp => by
    rw [elemWallUpPath, List.mem_append] at hp
    rcases hp with hp | hp
    · have hy := snd_of_mem_rowPath hp
      exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := snd_of_mem_elemWallUpPath x₂ hp
      exact ⟨by omega, by omega⟩

theorem nodup_elemWallUpPath (x₂ : ℕ) : ∀ (d x₁ y₁ : ℕ),
    (elemWallUpPath x₂ d x₁ y₁).Nodup
  | 0, x₁, y₁ => nodup_rowPath x₁ x₂ y₁
  | d + 1, x₁, y₁ => by
    rw [elemWallUpPath]
    refine (nodup_rowPath x₁ (vertCol y₁) y₁).append
      (nodup_elemWallUpPath x₂ d (vertCol y₁) (y₁ + 1)) ?_
    intro p hp₁ hp₂
    have hy₁ := snd_of_mem_rowPath hp₁
    have hy₂ := (snd_of_mem_elemWallUpPath x₂ hp₂).1
    omega

theorem isChain_elemWallUpPath {h x₂ : ℕ} (hh : 1 ≤ h) : ∀ (d x₁ y₁ : ℕ),
    (x₁, y₁) ∈ GM13.elementaryWallVerts h →
    (x₂, y₁ + d) ∈ GM13.elementaryWallVerts h →
    List.IsChain (GM13.elementaryWallAdj h) (elemWallUpPath x₂ d x₁ y₁)
  | 0, x₁, y₁, hx₁, hx₂ => by
    simpa [elemWallUpPath] using isChain_rowPath hx₁ hx₂
  | d + 1, x₁, y₁, hx₁, hx₂ => by
    have hy_le : y₁ + 1 ≤ h := by
      simp only [GM13.elementaryWallVerts, Set.mem_ofPred_eq] at hx₂
      omega
    have hc_y₁ : (vertCol y₁, y₁) ∈ GM13.elementaryWallVerts h :=
      vertCol_mem_elementaryWallVerts hh (by omega)
    have hc_succ : (vertCol y₁, y₁ + 1) ∈ GM13.elementaryWallVerts h :=
      vertCol_mem_elementaryWallVerts_succ hh hy_le
    have hchain₁ := isChain_rowPath hx₁ hc_y₁
    have hchain₂ := isChain_elemWallUpPath hh d (vertCol y₁) (y₁ + 1) hc_succ
      (by rwa [show y₁ + 1 + d = y₁ + (d + 1) by omega])
    rw [elemWallUpPath, List.isChain_append]
    refine ⟨hchain₁, hchain₂, ?_⟩
    intro a ha b hb
    rw [List.getLast?_eq_some_getLast (rowPath_ne_nil x₁ (vertCol y₁) y₁), Option.mem_def,
      Option.some.injEq] at ha
    rw [List.head?_eq_some_head (elemWallUpPath_ne_nil x₂ d (vertCol y₁) (y₁ + 1)), Option.mem_def,
      Option.some.injEq] at hb
    subst ha hb
    rw [getLast_rowPath, head_elemWallUpPath]
    exact elementaryWallAdj_vertCol hh hy_le

/-- Canonical simple path in `elementaryWall h` between coordinates `p` and `q`. -/
def elemWallCanonicalPath (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 ≤ q.2 then
    elemWallUpPath q.1 (q.2 - p.2) p.1 p.2
  else
    (elemWallUpPath p.1 (p.2 - q.2) q.1 q.2).reverse

theorem elemWallCanonicalPath_ne_nil (p q : ℕ × ℕ) :
    elemWallCanonicalPath p q ≠ [] := by
  unfold elemWallCanonicalPath
  split_ifs
  · exact elemWallUpPath_ne_nil _ _ _ _
  · exact List.reverse_ne_nil_iff.mpr (elemWallUpPath_ne_nil _ _ _ _)

theorem head_elemWallCanonicalPath (p q : ℕ × ℕ) :
    (elemWallCanonicalPath p q).head (elemWallCanonicalPath_ne_nil p q) = p := by
  unfold elemWallCanonicalPath
  split_ifs with hle
  · exact head_elemWallUpPath _ _ _ _
  · rw [List.head_reverse, getLast_elemWallUpPath]
    ext
    · rfl
    · dsimp; omega

theorem getLast_elemWallCanonicalPath (p q : ℕ × ℕ) :
    (elemWallCanonicalPath p q).getLast (elemWallCanonicalPath_ne_nil p q) = q := by
  unfold elemWallCanonicalPath
  split_ifs with hle
  · rw [getLast_elemWallUpPath]
    ext
    · rfl
    · dsimp; omega
  · rw [List.getLast_reverse, head_elemWallUpPath]

theorem nodup_elemWallCanonicalPath (p q : ℕ × ℕ) :
    (elemWallCanonicalPath p q).Nodup := by
  unfold elemWallCanonicalPath
  split_ifs
  · exact nodup_elemWallUpPath _ _ _ _
  · exact List.nodup_reverse.mpr (nodup_elemWallUpPath _ _ _ _)

theorem isChain_elemWallCanonicalPath {h : ℕ} (hh : 1 ≤ h) {p q : ℕ × ℕ}
    (hp : p ∈ GM13.elementaryWallVerts h) (hq : q ∈ GM13.elementaryWallVerts h) :
    List.IsChain (GM13.elementaryWallAdj h) (elemWallCanonicalPath p q) := by
  unfold elemWallCanonicalPath
  split_ifs with hle
  · exact isChain_elemWallUpPath hh (q.2 - p.2) p.1 p.2 hp
      (by
        have hq2 : p.2 + (q.2 - p.2) = q.2 := by omega
        rwa [hq2])
  · rw [List.isChain_reverse]
    have hc := isChain_elemWallUpPath hh (p.2 - q.2) q.1 q.2 hq
      (by
        have hp2 : q.2 + (p.2 - q.2) = p.2 := by omega
        rwa [hp2])
    exact hc.imp fun _ _ hadj => elementaryWallAdj_symm hadj


/-! ### Section 2: `suffixFrom`, `prefixUntil`, and `WallOfHeight.pathToSubwall` -/

/-- Suffix of `L` starting at the first occurrence of `u`. -/
def suffixFrom {α : Type*} [DecidableEq α] (u : α) : List α → List α
  | [] => []
  | x :: xs => if x = u then x :: xs else suffixFrom u xs

section SuffixFrom

variable {α : Type*} [DecidableEq α]

theorem suffixFrom_ne_nil {u : α} : ∀ {L : List α}, u ∈ L → suffixFrom u L ≠ []
  | [], hu => by nomatch hu
  | x :: xs, hu => by
    unfold suffixFrom
    split_ifs with hxu
    · exact List.cons_ne_nil _ _
    · rcases List.mem_cons.mp hu with rfl | htail
      · exact False.elim (hxu rfl)
      · exact suffixFrom_ne_nil htail

theorem head_suffixFrom {u : α} : ∀ {L : List α} (hu : u ∈ L),
    (suffixFrom u L).head (suffixFrom_ne_nil hu) = u
  | [], hu => by nomatch hu
  | x :: xs, hu => by
    unfold suffixFrom
    split_ifs with hxu
    · exact hxu
    · rcases List.mem_cons.mp hu with rfl | htail
      · exact False.elim (hxu rfl)
      · exact head_suffixFrom htail

theorem getLast_suffixFrom {u : α} : ∀ {L : List α} (hu : u ∈ L) (hne : L ≠ []),
    (suffixFrom u L).getLast (suffixFrom_ne_nil hu) = L.getLast hne
  | [], hu, _ => by nomatch hu
  | x :: xs, hu, _ => by
    unfold suffixFrom
    split_ifs with hxu
    · rfl
    · rcases List.mem_cons.mp hu with rfl | htail
      · exact False.elim (hxu rfl)
      · have hne_xs : xs ≠ [] := List.ne_nil_of_mem htail
        rw [getLast_suffixFrom htail hne_xs, List.getLast_cons hne_xs]

theorem mem_of_mem_suffixFrom {u : α} : ∀ {L : List α} {v : α},
    v ∈ suffixFrom u L → v ∈ L
  | [], _, hv => by nomatch hv
  | x :: xs, v, hv => by
    unfold suffixFrom at hv
    split_ifs at hv
    · exact hv
    · exact List.mem_cons_of_mem x (mem_of_mem_suffixFrom hv)

theorem mem_zip_of_mem_zip_suffixFrom {u : α} : ∀ {L : List α} {a b : α},
    (a, b) ∈ (suffixFrom u L).zip ((suffixFrom u L).drop 1) →
    (a, b) ∈ L.zip (L.drop 1)
  | [], _, _, hab => by nomatch hab
  | x :: xs, a, b, hab => by
    unfold suffixFrom at hab
    split_ifs at hab
    · exact hab
    · have ih := mem_zip_of_mem_zip_suffixFrom hab
      cases xs with
      | nil => nomatch ih
      | cons y ys => exact List.mem_cons_of_mem (x, y) ih

theorem nodup_suffixFrom {u : α} : ∀ {L : List α}, L.Nodup → (suffixFrom u L).Nodup
  | [], _ => List.nodup_nil
  | _ :: _, hnd => by
    unfold suffixFrom
    split_ifs
    · exact hnd
    · exact nodup_suffixFrom (List.nodup_cons.mp hnd).2

theorem isChain_suffixFrom {R : α → α → Prop} {u : α} : ∀ {L : List α},
    List.IsChain R L → List.IsChain R (suffixFrom u L)
  | [], _ => List.isChain_nil
  | _ :: _, hc => by
    unfold suffixFrom
    split_ifs
    · exact hc
    · exact isChain_suffixFrom (List.isChain_cons.mp hc).2

theorem isSimpleWalkList_suffixFrom {n : ℕ} {G : MultiDigraph n} {u : Fin n} :
    ∀ {L : List (Fin n)},
      WallOfHeight.IsSimpleWalkList G L →
      WallOfHeight.IsSimpleWalkList G (suffixFrom u L)
  | [], _ => trivial
  | x :: xs, hw => by
    unfold suffixFrom
    split_ifs
    · exact hw
    · cases xs with
      | nil => simp [suffixFrom, WallOfHeight.IsSimpleWalkList]
      | cons y ys => exact isSimpleWalkList_suffixFrom (L := y :: ys) hw.2

end SuffixFrom

/-- Prefix of `L` up to and including the first element in `S`. -/
def prefixUntil {α : Type*} [DecidableEq α] (S : Finset α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ S then [x] else x :: prefixUntil S xs

section PrefixUntil

variable {α : Type*} [DecidableEq α] (S : Finset α)

theorem prefixUntil_ne_nil : ∀ {L : List α}, L ≠ [] → prefixUntil S L ≠ []
  | [], hne => False.elim (hne rfl)
  | x :: xs, _ => by
    unfold prefixUntil
    split_ifs <;> exact List.cons_ne_nil _ _

theorem head_prefixUntil : ∀ {L : List α} (hne : L ≠ []),
    (prefixUntil S L).head (prefixUntil_ne_nil S hne) = L.head hne
  | [], hne => False.elim (hne rfl)
  | x :: xs, _ => by
    unfold prefixUntil
    split_ifs <;> rfl

theorem getLast_prefixUntil_mem : ∀ {L : List α} (hne : L ≠ []),
    L.getLast hne ∈ S → (prefixUntil S L).getLast (prefixUntil_ne_nil S hne) ∈ S
  | [], hne, _ => False.elim (hne rfl)
  | [x], _, hlast => by
    unfold prefixUntil
    split_ifs with hx
    · exact hx
    · simpa [prefixUntil] using hlast
  | x :: y :: xs, _, hlast => by
    unfold prefixUntil
    split_ifs with hx
    · exact hx
    · have hne' : prefixUntil S (y :: xs) ≠ [] := prefixUntil_ne_nil S (List.cons_ne_nil y xs)
      rw [List.getLast_cons hne']
      exact getLast_prefixUntil_mem (List.cons_ne_nil y xs) hlast

theorem eq_getLast_of_mem_prefixUntil : ∀ {L : List α} (hne : L ≠ []) {v : α},
    v ∈ prefixUntil S L → v ∈ S →
    v = (prefixUntil S L).getLast (prefixUntil_ne_nil S hne)
  | [], hne, _, _, _ => False.elim (hne rfl)
  | x :: xs, _, v, hv, hvS => by
    unfold prefixUntil at hv ⊢
    split_ifs at hv ⊢ with hx
    · simp only [List.mem_singleton] at hv
      exact hv
    · rcases List.mem_cons.mp hv with rfl | htail
      · exact False.elim (hx hvS)
      · have hne_xs : xs ≠ [] := by
          rintro rfl
          simp [prefixUntil] at htail
        have hne_pref : prefixUntil S xs ≠ [] := prefixUntil_ne_nil S hne_xs
        rw [List.getLast_cons hne_pref]
        exact eq_getLast_of_mem_prefixUntil hne_xs htail hvS

theorem mem_of_mem_prefixUntil : ∀ {L : List α} {v : α},
    v ∈ prefixUntil S L → v ∈ L
  | [], _, hv => by nomatch hv
  | x :: xs, v, hv => by
    unfold prefixUntil at hv
    split_ifs at hv
    · simp only [List.mem_singleton] at hv
      exact hv ▸ List.mem_cons_self
    · rcases List.mem_cons.mp hv with rfl | htail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (mem_of_mem_prefixUntil htail)

theorem mem_zip_of_mem_zip_prefixUntil : ∀ {L : List α} {a b : α},
    (a, b) ∈ (prefixUntil S L).zip ((prefixUntil S L).drop 1) →
    (a, b) ∈ L.zip (L.drop 1)
  | [], _, _, hab => by nomatch hab
  | [x], _, _, hab => by
    unfold prefixUntil at hab
    split_ifs at hab <;> simp [prefixUntil] at hab
  | x :: y :: xs, a, b, hab => by
    unfold prefixUntil at hab
    split_ifs at hab with hx
    · simp at hab
    · have hhead : prefixUntil S (y :: xs) = y :: (prefixUntil S (y :: xs)).drop 1 := by
        unfold prefixUntil
        split_ifs <;> rfl
      rw [hhead] at hab
      rcases List.mem_cons.mp hab with ⟨rfl, rfl⟩ | htail
      · exact List.mem_cons_self
      · rw [← hhead] at htail
        exact List.mem_cons_of_mem (x, y) (mem_zip_of_mem_zip_prefixUntil htail)

theorem nodup_prefixUntil : ∀ {L : List α}, L.Nodup → (prefixUntil S L).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    unfold prefixUntil
    split_ifs
    · exact List.nodup_singleton x
    · rw [List.nodup_cons] at hnd ⊢
      exact ⟨fun hmem => hnd.1 (mem_of_mem_prefixUntil S hmem), nodup_prefixUntil hnd.2⟩

end PrefixUntil

theorem isSimpleWalkList_prefixUntil {n : ℕ} {G : MultiDigraph n} (S : Finset (Fin n)) :
    ∀ {L : List (Fin n)},
      WallOfHeight.IsSimpleWalkList G L →
      WallOfHeight.IsSimpleWalkList G (prefixUntil S L)
  | [], _ => trivial
  | [x], _ => by
    unfold prefixUntil
    split_ifs <;> simp [prefixUntil, WallOfHeight.IsSimpleWalkList]
  | x :: y :: xs, hw => by
    unfold prefixUntil
    split_ifs with hx
    · trivial
    · have ih := isSimpleWalkList_prefixUntil S (L := y :: xs) hw.2
      have hhead : prefixUntil S (y :: xs) = y :: (prefixUntil S (y :: xs)).drop 1 := by
        unfold prefixUntil
        split_ifs <;> rfl
      rw [hhead] at ih ⊢
      exact ⟨hw.1, ih⟩

/-- Canonical path in `elementaryWall h` starting with edge `(p₁, p₂)` or `(p₂, p₁)` and ending at
`q`. -/
def elemWallEdgeCanonicalPath (p₁ p₂ q : ℕ × ℕ) : List (ℕ × ℕ) :=
  let L := elemWallCanonicalPath p₁ q
  if p₂ ∈ L then
    p₁ :: suffixFrom p₂ L
  else
    p₂ :: L

theorem elemWallEdgeCanonicalPath_props {h : ℕ} (hh : 1 ≤ h) {p₁ p₂ q : ℕ × ℕ}
    (hadj : GM13.elementaryWallAdj h p₁ p₂) (hq : q ∈ GM13.elementaryWallVerts h) :
    let P := elemWallEdgeCanonicalPath p₁ p₂ q
    ∃ hne : P ≠ [],
      P.head hne ∈ GM13.elementaryWallVerts h ∧
      P.getLast hne = q ∧
      List.IsChain (GM13.elementaryWallAdj h) P ∧
      P.Nodup ∧
      ((∃ rest, P = p₁ :: p₂ :: rest) ∨ (∃ rest, P = p₂ :: p₁ :: rest)) := by
  have hp₁ : p₁ ∈ GM13.elementaryWallVerts h := hadj.1
  have hp₂ : p₂ ∈ GM13.elementaryWallVerts h := hadj.2.1
  have hne_p : p₁ ≠ p₂ := by
    rcases hadj.2.2 with ⟨_, _ | _⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ <;> intro heq <;>
      rcases Prod.mk.inj heq with ⟨_, _⟩ <;> omega
  let L := elemWallCanonicalPath p₁ q
  have hneL : L ≠ [] := elemWallCanonicalPath_ne_nil p₁ q
  have hheadL : L.head hneL = p₁ := head_elemWallCanonicalPath p₁ q
  have hlastL : L.getLast hneL = q := getLast_elemWallCanonicalPath p₁ q
  have hcL : List.IsChain (GM13.elementaryWallAdj h) L := isChain_elemWallCanonicalPath hh hp₁ hq
  have hndL : L.Nodup := nodup_elemWallCanonicalPath p₁ q
  dsimp only [elemWallEdgeCanonicalPath]
  split_ifs with hp₂_mem
  · have hneS : suffixFrom p₂ L ≠ [] := suffixFrom_ne_nil hp₂_mem
    have hheadS : (suffixFrom p₂ L).head hneS = p₂ := head_suffixFrom hp₂_mem
    have hlastS : (suffixFrom p₂ L).getLast hneS = q :=
      (getLast_suffixFrom hp₂_mem hneL).trans hlastL
    have hcS : List.IsChain (GM13.elementaryWallAdj h) (suffixFrom p₂ L) := isChain_suffixFrom hcL
    have hndS : (suffixFrom p₂ L).Nodup := nodup_suffixFrom hndL
    have hp₁_not_mem : p₁ ∉ suffixFrom p₂ L := by
      rcases List.exists_cons_of_ne_nil hneL with ⟨x, xs, hL_eq⟩
      have hx : x = p₁ := by
        rw [← hheadL]
        simp [hL_eq]
      subst x
      have hp₁_xs : p₁ ∉ xs := by
        rw [hL_eq, List.nodup_cons] at hndL
        exact hndL.1
      have hS_eq : suffixFrom p₂ L = suffixFrom p₂ xs := by
        rw [hL_eq, suffixFrom, ite_eq_right_iff.mpr (fun h => False.elim (hne_p h))]
      rw [hS_eq]
      intro hmem
      exact hp₁_xs (mem_of_mem_suffixFrom hmem)
    refine ⟨List.cons_ne_nil _ _, hp₁, ?_, ?_, List.nodup_cons.mpr ⟨hp₁_not_mem, hndS⟩, ?_⟩
    · rw [List.getLast_cons hneS, hlastS]
    · rw [List.isChain_cons]
      refine ⟨?_, hcS⟩
      intro y hy
      rw [List.head?_eq_some_head hneS, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hheadS]
      exact hadj
    · rcases List.exists_cons_of_ne_nil hneS with ⟨y, ys, hS_cons⟩
      have hy : y = p₂ := by
        rw [← hheadS]
        simp [hS_cons]
      subst y
      exact Or.inl ⟨ys, congrArg (p₁ :: ·) hS_cons⟩
  · refine ⟨List.cons_ne_nil _ _, hp₂, ?_, ?_, List.nodup_cons.mpr ⟨hp₂_mem, hndL⟩, ?_⟩
    · rw [List.getLast_cons hneL, hlastL]
    · rw [List.isChain_cons]
      refine ⟨?_, hcL⟩
      intro y hy
      rw [List.head?_eq_some_head hneL, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hheadL]
      exact elementaryWallAdj_symm hadj
    · rcases List.exists_cons_of_ne_nil hneL with ⟨y, ys, hL_cons⟩
      have hy : y = p₁ := by
        rw [← hheadL]
        simp [hL_cons]
      subst y
      exact Or.inr ⟨ys, congrArg (p₂ :: ·) hL_cons⟩

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

/-- Elementary-wall coordinate chain for `v ∈ W.vertexFinset` ending at `q`. -/
def elemPathForVert (v : Fin n) (q : ℕ × ℕ) : List (ℕ × ℕ) :=
  match (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u => elemWallCanonicalPath (elemWallVertCoord h u) q
  | none =>
    match (List.finRange (elemWallEdges h).length).find? (fun k => decide (v ∈ W.internalVerts k)) with
    | some k =>
      let e := (elemWallEdges h)[k.1]'k.2
      elemWallEdgeCanonicalPath (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) q
    | none => [q]

theorem elemPathForVert_props (hh : 1 ≤ h) {v : Fin n} (hv : v ∈ W.vertexFinset)
    {q : ℕ × ℕ} (hq : q ∈ GM13.elementaryWallVerts h) :
    let P := W.elemPathForVert v q
    ∃ hne : P ≠ [],
      P.head hne ∈ GM13.elementaryWallVerts h ∧
      P.getLast hne = q ∧
      List.IsChain (GM13.elementaryWallAdj h) P ∧
      P.Nodup ∧
      v ∈ W.liftElemPath P := by
  unfold elemPathForVert
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u =>
    have hu : W.branchVert u = v := by simpa using List.find?_some hfind1
    let p := elemWallVertCoord h u
    have hp : p ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h u
    have hne := elemWallCanonicalPath_ne_nil p q
    have hhead := head_elemWallCanonicalPath p q
    have hlast := getLast_elemWallCanonicalPath p q
    have hc := isChain_elemWallCanonicalPath hh hp hq
    have hnd := nodup_elemWallCanonicalPath p q
    dsimp only
    refine ⟨hne, hhead.symm ▸ hp, hlast, hc, hnd, ?_⟩
    rcases List.exists_cons_of_ne_nil hne with ⟨a, rest, hcons⟩
    have ha : a = p := by
      rw [← hhead]
      simp [hcons]
    subst ha
    rw [hcons]
    obtain ⟨hne_lift, hhead_lift⟩ := W.liftElemPath_ne_nil_and_head (rest := rest) hp
    have hv_eq : v = (W.liftElemPath (p :: rest)).head hne_lift := by
      rw [hhead_lift, elemWallCoordIdx_elemWallVertCoord, hu]
    rw [hv_eq]
    exact List.head_mem hne_lift
  | none =>
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | none =>
      rcases W.mem_vertexFinset_cases hv with ⟨u, hu⟩ | ⟨k, hvk⟩
      · have hnone := List.find?_eq_none.mp hfind1 u (List.mem_finRange u)
        simp [hu] at hnone
      · have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
        simp [hvk] at hnone
    | some k =>
      have hvk : v ∈ W.internalVerts k := by simpa using List.find?_some hfind2
      let e := (elemWallEdges h)[k.1]'k.2
      let p₁ := elemWallVertCoord h e.1
      let p₂ := elemWallVertCoord h e.2
      have hadj : GM13.elementaryWallAdj h p₁ p₂ := elemWallEdge_elementaryWallAdj h k
      obtain ⟨hne, hhead_mem, hlast, hc, hnd, hcases⟩ := elemWallEdgeCanonicalPath_props hh hadj hq
      dsimp only
      refine ⟨hne, hhead_mem, hlast, hc, hnd, ?_⟩
      rcases hcases with ⟨rest, hcons⟩ | ⟨rest, hcons⟩
      · rw [hcons, liftElemPath, List.mem_append, List.mem_append]
        refine Or.inl (Or.inr ?_)
        rcases W.mem_stepInternalVerts_iff hadj v with ⟨k', hk', hiff⟩
        have hkeq : k' = k := elemWallEdgeSym2_injective h hk'
        exact hiff.mpr (hkeq ▸ hvk)
      · rw [hcons, liftElemPath, List.mem_append, List.mem_append]
        refine Or.inl (Or.inr ?_)
        have hadj_symm : GM13.elementaryWallAdj h p₂ p₁ := elementaryWallAdj_symm hadj
        rcases W.mem_stepInternalVerts_iff hadj_symm v with ⟨k', hk', hiff⟩
        have hkeq : k' = k := elemWallEdgeSym2_injective h (hk'.trans Sym2.eq_swap)
        exact hiff.mpr (hkeq ▸ hvk)

theorem mem_vertexFinset_of_mem_liftElemPath {a : ℕ × ℕ} {rest : List (ℕ × ℕ)} {v : Fin n}
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (ha : a ∈ GM13.elementaryWallVerts h)
    (hv : v ∈ W.liftElemPath (a :: rest)) :
    v ∈ W.vertexFinset := by
  rcases W.mem_liftElemPath_cases hc ha hv with ⟨u, hu, _, rfl⟩ | ⟨uw, huw, hvuw⟩
  · exact W.branchVert_mem_vertexFinset _
  · have huw_adj : GM13.elementaryWallAdj h uw.1 uw.2 :=
      GM13.List.rel_of_mem_zip_of_isChain hc uw huw
    rcases W.mem_stepInternalVerts_iff huw_adj v with ⟨k, _, hiff⟩
    exact W.mem_vertexFinset_of_mem_internalVerts (hiff.mp hvuw)

theorem elemWallCoordIdx_eq_of_eq {p q : ℕ × ℕ}
    (hp : p ∈ GM13.elementaryWallVerts h) (hq : q ∈ GM13.elementaryWallVerts h) (heq : p = q) :
    elemWallCoordIdx h p hp = elemWallCoordIdx h q hq := by
  subst heq
  rfl

/-- Computable minimal path in `W` from `v ∈ W.vertexFinset` to `S`, heading toward branch vertex
coordinate `q`. -/
def pathToSubwall (S : Finset (Fin n)) (v : Fin n) (q : ℕ × ℕ) : List (Fin n) :=
  prefixUntil S (suffixFrom v (W.liftElemPath (W.elemPathForVert v q)))

theorem pathToSubwall_props (hh : 1 ≤ h) (hW : W.IsValid) {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ W.vertexFinset) {q : ℕ × ℕ} (hq : q ∈ GM13.elementaryWallVerts h)
    (hTarget : W.branchVert (elemWallCoordIdx h q hq) ∈ S) :
    let Q := W.pathToSubwall S v q
    ∃ hne : Q ≠ [],
      Q.head hne = v ∧
      Q.getLast hne ∈ S ∧
      (∀ x ∈ Q, x ∈ S → x = Q.getLast hne) ∧
      Q.Nodup ∧
      IsSimpleWalkList G Q ∧
      (∀ x ∈ Q, x ∈ W.vertexFinset) ∧
      (∀ a b, (a, b) ∈ Q.zip (Q.drop 1) → W.IsWallEdge a b) := by
  obtain ⟨hneP, hheadP, hlastP, hcP, hndP, hv_lift⟩ := W.elemPathForVert_props hh hv hq
  rcases List.exists_cons_of_ne_nil hneP with ⟨a, rest, hP_cons⟩
  have ha : a ∈ GM13.elementaryWallVerts h := by
    have : a = (W.elemPathForVert v q).head hneP := by simp [hP_cons]
    exact this ▸ hheadP
  have hc_cons : List.IsChain (GM13.elementaryWallAdj h) (a :: rest) := hP_cons ▸ hcP
  have hnd_cons : (a :: rest).Nodup := hP_cons ▸ hndP
  have hv_cons : v ∈ W.liftElemPath (a :: rest) := hP_cons ▸ hv_lift
  obtain ⟨hneL, _⟩ := W.liftElemPath_ne_nil_and_head (rest := rest) ha
  have hlastL : (W.liftElemPath (a :: rest)).getLast hneL =
      W.branchVert (elemWallCoordIdx h q hq) := by
    have h1 := W.liftElemPath_getLast hc_cons ha hneL
    dsimp only at h1
    have hlast_eq : (a :: rest).getLast (List.cons_ne_nil a rest) = q := by
      rw [← hlastP]
      simp [hP_cons]
    rw [h1]
    exact congrArg W.branchVert (elemWallCoordIdx_eq_of_eq _ hq hlast_eq)
  have hndL : (W.liftElemPath (a :: rest)).Nodup := W.nodup_liftElemPath hW hc_cons ha hnd_cons
  have hwL : IsSimpleWalkList G (W.liftElemPath (a :: rest)) :=
    W.isSimpleWalkList_liftElemPath hW hc_cons ha
  have hVL : ∀ x ∈ W.liftElemPath (a :: rest), x ∈ W.vertexFinset := fun x hx =>
    W.mem_vertexFinset_of_mem_liftElemPath hc_cons ha hx
  have hEL : ∀ x y, (x, y) ∈ (W.liftElemPath (a :: rest)).zip ((W.liftElemPath (a :: rest)).drop 1) →
      W.IsWallEdge x y :=
    W.isWallEdge_of_mem_zip_liftElemPath hc_cons ha
  have hneS : suffixFrom v (W.liftElemPath (a :: rest)) ≠ [] := suffixFrom_ne_nil hv_cons
  have hheadS : (suffixFrom v (W.liftElemPath (a :: rest))).head hneS = v := head_suffixFrom hv_cons
  have hlastS : (suffixFrom v (W.liftElemPath (a :: rest))).getLast hneS ∈ S := by
    rw [getLast_suffixFrom hv_cons hneL, hlastL]
    exact hTarget
  dsimp only [pathToSubwall]
  change ∃ hne : prefixUntil S (suffixFrom v (W.liftElemPath (W.elemPathForVert v q))) ≠ [], _
  simp only [hP_cons]
  have hneQ : prefixUntil S (suffixFrom v (W.liftElemPath (a :: rest))) ≠ [] :=
    prefixUntil_ne_nil S hneS
  refine ⟨hneQ,
    (head_prefixUntil S hneS).trans hheadS,
    getLast_prefixUntil_mem S hneS hlastS,
    fun x hx hxS => eq_getLast_of_mem_prefixUntil S hneS hx hxS,
    nodup_prefixUntil S (nodup_suffixFrom hndL),
    isSimpleWalkList_prefixUntil S (isSimpleWalkList_suffixFrom hwL),
    fun x hx => hVL x (mem_of_mem_suffixFrom (mem_of_mem_prefixUntil S hx)),
    fun x y hxy => hEL x y (mem_zip_of_mem_zip_suffixFrom (mem_zip_of_mem_zip_prefixUntil S hxy))⟩

theorem mem_vertexFinset_of_isWallEdge {u v : Fin n} (huv : W.IsWallEdge u v) :
    u ∈ W.vertexFinset ∧ v ∈ W.vertexFinset := by
  rcases huv with ⟨k, h1 | h2⟩
  · have hu : u ∈ W.subdivPathVerts k := (List.of_mem_zip h1).1
    have hv : v ∈ W.subdivPathVerts k := List.mem_of_mem_drop (List.of_mem_zip h1).2
    refine ⟨?_, ?_⟩
    · rcases (W.mem_subdivPathVerts_iff k u).mp hu with rfl | hint | rfl
      · exact W.branchVert_mem_vertexFinset _
      · exact W.mem_vertexFinset_of_mem_internalVerts hint
      · exact W.branchVert_mem_vertexFinset _
    · rcases (W.mem_subdivPathVerts_iff k v).mp hv with rfl | hint | rfl
      · exact W.branchVert_mem_vertexFinset _
      · exact W.mem_vertexFinset_of_mem_internalVerts hint
      · exact W.branchVert_mem_vertexFinset _
  · have hv : v ∈ W.subdivPathVerts k := (List.of_mem_zip h2).1
    have hu : u ∈ W.subdivPathVerts k := List.mem_of_mem_drop (List.of_mem_zip h2).2
    refine ⟨?_, ?_⟩
    · rcases (W.mem_subdivPathVerts_iff k u).mp hu with rfl | hint | rfl
      · exact W.branchVert_mem_vertexFinset _
      · exact W.mem_vertexFinset_of_mem_internalVerts hint
      · exact W.branchVert_mem_vertexFinset _
    · rcases (W.mem_subdivPathVerts_iff k v).mp hv with rfl | hint | rfl
      · exact W.branchVert_mem_vertexFinset _
      · exact W.mem_vertexFinset_of_mem_internalVerts hint
      · exact W.branchVert_mem_vertexFinset _


/-! ### Section 3: Lifting Wall Paths to `(W.toGMWall h2 he hW).graph` and Distance Preservation -/

theorem isLink_adjEdgeTriple_of_mem_zip_toGMGraphWalk :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hw : IsSimpleWalkList G L) {u v : Fin n},
      (u, v) ∈ L.zip (L.drop 1) →
      (GM09.walkSubgraph (toGMGraphWalk hne hw)).IsLink (adjEdgeTriple G u v) u.1 v.1
  | [], hne, _, _, _, _ => False.elim (hne rfl)
  | [_], _, _, _, _, huv => by nomatch huv
  | x :: y :: rest, _, hw, u, v, huv => by
    rcases List.mem_cons.mp huv with ⟨rfl, rfl⟩ | htail
    · rw [GM09.walkSubgraph_isLink]
      exact ⟨List.mem_cons_self, isLink_adjEdgeTriple hw.1⟩
    · have ih := isLink_adjEdgeTriple_of_mem_zip_toGMGraphWalk (List.cons_ne_nil y rest) hw.2 htail
      rw [GM09.walkSubgraph_isLink] at ih ⊢
      exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩

theorem exists_isLink_toGMWall_of_isWallEdge (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u v : Fin n} (huv : W.IsWallEdge u v) :
    ∃ b : ℕ × ℕ × ℕ, (W.toGMWall h2 he hW).graph.IsLink b u.1 v.1 := by
  rcases huv with ⟨k, h1 | h2_zip⟩
  · have hlink_sub : (W.subdivPathGraph hW k).IsLink (adjEdgeTriple G u v) u.1 v.1 :=
      isLink_adjEdgeTriple_of_mem_zip_toGMGraphWalk (W.subdivPathVerts_ne_nil k) (hW.2.1 k).2 h1
    have hle : W.subdivPathGraph hW k ≤ (W.toGMWall h2 he hW).graph := by
      rw [W.toGMWall_graph, ← W.subdivPathOfSym2_elemWallEdgeSym2 hW k]
      exact W.subdivPathOfSym2_le_toGMGraph hW (elemWallEdgeSym2_mem_edgeSet h k)
    exact ⟨adjEdgeTriple G u v, hle.isLink_mono hlink_sub⟩
  · have hlink_sub : (W.subdivPathGraph hW k).IsLink (adjEdgeTriple G v u) v.1 u.1 :=
      isLink_adjEdgeTriple_of_mem_zip_toGMGraphWalk (W.subdivPathVerts_ne_nil k) (hW.2.1 k).2 h2_zip
    have hle : W.subdivPathGraph hW k ≤ (W.toGMWall h2 he hW).graph := by
      rw [W.toGMWall_graph, ← W.subdivPathOfSym2_elemWallEdgeSym2 hW k]
      exact W.subdivPathOfSym2_le_toGMGraph hW (elemWallEdgeSym2_mem_edgeSet h k)
    exact ⟨adjEdgeTriple G v u, (hle.isLink_mono hlink_sub).symm⟩

theorem exists_isGraphPathWithEnds_toGMWall_of_isWallEdge (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    ∀ {Q : List (Fin n)} (hne : Q ≠ []),
      Q.Nodup →
      (∀ x ∈ Q, x ∈ W.vertexFinset) →
      (∀ a b, (a, b) ∈ Q.zip (Q.drop 1) → W.IsWallEdge a b) →
      ∃ Q_graph : Graph ℕ (ℕ × ℕ × ℕ),
        GM09.IsGraphPathWithEnds (W.toGMWall h2 he hW).graph Q_graph
          (Q.head hne).1 (Q.getLast hne).1 ∧
        V(Q_graph) = {x : ℕ | x ∈ Q.map Fin.val} := by
  have hwalk : ∀ {Q : List (Fin n)} (hne : Q ≠ []),
      (∀ x ∈ Q, x ∈ W.vertexFinset) →
      (∀ a b, (a, b) ∈ Q.zip (Q.drop 1) → W.IsWallEdge a b) →
      ∃ w : GraphWalk (W.toGMWall h2 he hW).graph (Q.head hne).1 (Q.getLast hne).1,
        w.support = Q.map Fin.val := by
    intro Q
    induction Q with
    | nil => intro hne; exact False.elim (hne rfl)
    | cons u rest ih =>
      intro hne hV hE
      cases rest with
      | nil =>
        have hu : u.1 ∈ V((W.toGMWall h2 he hW).graph) :=
          (W.mem_vertexFinset_iff_val_mem_toGMWall h2 he hW u).mp (hV u List.mem_cons_self)
        exact ⟨.nil hu, rfl⟩
      | cons v ys =>
        have huv : W.IsWallEdge u v := hE u v List.mem_cons_self
        obtain ⟨b, hlink⟩ := W.exists_isLink_toGMWall_of_isWallEdge h2 he hW huv
        obtain ⟨w_rest, hsupp⟩ := ih (List.cons_ne_nil v ys)
          (fun x hx => hV x (List.mem_cons_of_mem u hx))
          (fun x y hxy => hE x y (List.mem_cons_of_mem (u, v) hxy))
        exact ⟨.cons hlink w_rest, congrArg (u.1 :: ·) hsupp⟩
  intro Q hne hnd hV hE
  obtain ⟨w, hsupp⟩ := hwalk hne hV hE
  have hsimp : w.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hsupp]
    exact hnd.map Fin.val_injective
  refine ⟨GM09.walkSubgraph w, GM09.isGraphPathWithEnds_walkSubgraph hsimp, ?_⟩
  rw [GM09.vertexSet_walkSubgraph, hsupp]

end WallOfHeight

theorem drawnOnCells_planeWallDist_eq_fig1CellBrickDist
    {G₀ : Graph ℕ (ℕ × ℕ × ℕ)} {Γ : Surface.GraphDrawing G₀ Surface.EuclideanPlane}
    {W₀ : GM13.Wall ℕ (ℕ × ℕ × ℕ)} {C₀ : GM13.CellWall W₀.height}
    (hh₀ : 1 ≤ W₀.height) (hD : GM13.DrawnOnCells Γ W₀ C₀) (hle : W₀.graph ≤ G₀)
    {m₁ m₂ : ℤ × ℤ} (hm₁ : m₁ ∈ GM13.fig1WallCells W₀.height)
    (hm₂ : m₂ ∈ GM13.fig1WallCells W₀.height)
    {x y : ℕ} (hx : x ∈ W₀.elemV m₁) (hy : y ∈ W₀.elemV m₂) (hne : x ≠ y) :
    GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C₀.𝒰)
      (GM13.ptV Γ x) (GM13.ptV Γ y) = fig1CellBrickDist W₀.height m₁ m₂ := by
  obtain ⟨s, hs, es⟩ := hD.exists_cell hm₁ hx
  obtain ⟨t, ht, et⟩ := hD.exists_cell hm₂ hy
  have hst : s ≠ t := fun e =>
    hne (GM13.ptV_injOn Γ (hle.vertexSet_mono (W₀.elemV_subset m₁ hx))
      (hle.vertexSet_mono (W₀.elemV_subset m₂ hy)) (by rw [es, et, e]))
  rw [es, et]
  by_cases hne_m : m₁ = m₂
  · subst hne_m
    have hle2 : GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C₀.𝒰)
        (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) ≤ 2 :=
      C₀.planeWallDist_le_two hm₁ hs ht
    have hge2 : 2 ≤ GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C₀.𝒰)
        (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) :=
      GM13.CellWall.two_le_planeWallDist C₀.naming.not_square
        (GM13.fig1PlaneEquiv.injective.ne hst)
        ⟨s, C₀.mem_U_of_mem_cells hm₁ hs, rfl⟩
        ⟨t, C₀.mem_U_of_mem_cells hm₁ ht, rfl⟩
    have hf_le2 : fig1CellBrickDist W₀.height m₁ m₁ ≤ 2 :=
      fig1CellBrickDist_self_le_two W₀.height m₁
    have hf_ge2 : 2 ≤ fig1CellBrickDist W₀.height m₁ m₁ := by
      unfold fig1CellBrickDist
      have hc : GM13.cellInd (GM13.fig1WallCells W₀.height) m₁ = 1 :=
        GM13.cellInd_of_mem hm₁
      omega
    omega
  · exact cellWall_planeWallDist_eq_fig1CellBrickDist hh₀ W₀.even_height C₀ hm₁ hm₂ hne_m hs ht

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

/-- Two vertices `u, v ∈ W.vertexFinset` have `W.brickDist u v ≤ 2 * h + 2`. -/
theorem brickDist_le_two_mul_height_add_two (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u v : Fin n} (hu : u ∈ W.vertexFinset) (hv : v ∈ W.vertexFinset) :
    W.brickDist u v ≤ 2 * h + 2 := by
  by_cases huv : u = v
  · subst huv
    simp [brickDist]
  · let H := W.toGMWall h2 he hW
    obtain ⟨Γ, hΓ⟩ := H.exists_isFigure1CoordDrawing
    let D : GM13.DrawnWall ℕ (ℕ × ℕ × ℕ) :=
      { H with
        drawingU := Γ.drawing.U
        vertexPoint := GM13.ptV Γ
        vertexPoint_mem := fun x hx => Γ.drawing.V_subset_U (GM13.ptV_mem_V Γ hx)
        vertexPoint_injOn := GM13.ptV_injOn Γ }
    have hDF : D.IsFigure1 :=
      ⟨Homeomorph.refl _, Γ, hΓ, by simp [D], fun x hx => GM13.ptV_of_mem Γ hx⟩
    have huH : u.1 ∈ V(H.graph) := (W.mem_vertexFinset_iff_val_mem_toGMWall h2 he hW u).mp hu
    have hvH : v.1 ∈ V(H.graph) := (W.mem_vertexFinset_iff_val_mem_toGMWall h2 he hW v).mp hv
    have hle := hDF.dist_le huH hvH
    have hH_height : H.height = h := rfl
    have hD_height : D.height = h := rfl
    have hD := GM13.drawnOnCells_fig1 hΓ (by omega) H.even_height
    have hdist_eq : D.dist u.1 v.1 = W.brickDist u v := by
      change GM13.planeWallDist Γ.drawing.U (GM13.ptV Γ u.1) (GM13.ptV Γ v.1) = _
      rw [hΓ.drawing_U_eq, GM13.fig1WallSet_eq_cellSet]
      have h1 := drawnOnCells_planeWallDist_eq_fig1CellBrickDist (by omega) hD le_rfl
        (W.vertCell_mem_fig1WallCells h2 he hW hu)
        (W.vertCell_mem_fig1WallCells h2 he hW hv)
        (W.val_mem_toGMWall_elemV_vertCell h2 he hW hu)
        (W.val_mem_toGMWall_elemV_vertCell h2 he hW hv)
        (fun e => huv (Fin.ext e))
      have hU : GM13.fig1WallCells H.height = (GM13.CellWall.fig1 (by omega) H.even_height).𝒰 := rfl
      have hbrick : W.brickDist u v = fig1CellBrickDist h (W.vertCell u) (W.vertCell v) := by
        simp [brickDist, huv]
      rw [hU, h1, hH_height, ← hbrick]
    rw [hdist_eq, hD_height] at hle
    exact hle

/-- If `Q₁, Q₂` are minimal paths in `W` from `u₁, u₂ ∈ W.vertexFinset` to `W' = W.realizeSubwall R`
(where `τ.DepthTest` holds) and `d ≤ W.brickDist u₁ u₂` with `7 ≤ d`, then `Q₁` and `Q₂` are
vertex-disjoint and their endpoints `w₁, w₂` satisfy `d - 4 ≤ W'.brickDist w₁ w₂`. -/
theorem disjoint_and_brickDist_ge_of_paths_to_realizeSubwall
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} (h2' : 2 ≤ h') (he' : Even h')
    {τ : GM13.Shape h h'} (R : τ.Realization) (hdepth : τ.DepthTest)
    {u₁ u₂ w₁ w₂ : Fin n} {Q₁ Q₂ : List (Fin n)}
    (hu₁ : u₁ ∈ W.vertexFinset) (hu₂ : u₂ ∈ W.vertexFinset)
    (hne₁ : Q₁ ≠ []) (hhead₁ : Q₁.head hne₁ = u₁) (hlast₁ : Q₁.getLast hne₁ = w₁)
    (hw₁ : w₁ ∈ (W.realizeSubwall R).vertexFinset)
    (hX₁ : ∀ x ∈ Q₁, x ∈ (W.realizeSubwall R).vertexFinset → x = w₁)
    (hnd₁ : Q₁.Nodup) (hV₁ : ∀ x ∈ Q₁, x ∈ W.vertexFinset)
    (hE₁ : ∀ a b, (a, b) ∈ Q₁.zip (Q₁.drop 1) → W.IsWallEdge a b)
    (hne₂ : Q₂ ≠ []) (hhead₂ : Q₂.head hne₂ = u₂) (hlast₂ : Q₂.getLast hne₂ = w₂)
    (hw₂ : w₂ ∈ (W.realizeSubwall R).vertexFinset)
    (hX₂ : ∀ x ∈ Q₂, x ∈ (W.realizeSubwall R).vertexFinset → x = w₂)
    (hnd₂ : Q₂.Nodup) (hV₂ : ∀ x ∈ Q₂, x ∈ W.vertexFinset)
    (hE₂ : ∀ a b, (a, b) ∈ Q₂.zip (Q₂.drop 1) → W.IsWallEdge a b)
    {d : ℕ} (hd7 : 7 ≤ d) (hdist : d ≤ W.brickDist u₁ u₂) :
    (∀ x, x ∈ Q₁ → x ∈ Q₂ → False) ∧
    d - 4 ≤ (W.realizeSubwall R).brickDist w₁ w₂ := by
  have hh1 : 1 ≤ h := by omega
  have hh'1 : 1 ≤ h' := by omega
  have hu_ne : u₁ ≠ u₂ := by
    rintro rfl
    simp [brickDist] at hdist
    omega
  let H := W.toGMWall h2 he hW
  obtain ⟨Γ, hΓ⟩ := H.exists_isFigure1CoordDrawing
  let C := GM13.CellWall.fig1 hh1 he
  have hD : GM13.DrawnOnCells Γ H C := GM13.drawnOnCells_fig1 hΓ hh1 he
  let W'_gm := R.wall H hh'1 he'
  let C' := C.transform τ hh'1 he'
  have hle : W'_gm.graph ≤ H.graph := R.wall_graph_le H hh'1 he'
  have hD' : GM13.DrawnOnCells Γ W'_gm C' := hD.wall R hh'1 he'
  have hH_height : H.height = h := rfl
  have hW'_height : W'_gm.height = h' := rfl
  have htrans_fn : GM13.DistGeSub
      (GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C'.𝒰))
      (GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C.𝒰)) 4 :=
    C.transform_distGeSub τ hh'1 he' (by norm_num) hdepth.ki
  have htrans := htrans_fn (GM13.ptV Γ u₁.1) (GM13.ptV Γ u₂.1)
  have hdist_u : GM13.planeWallDist (GM13.fig1PlaneEquiv '' GM13.cellSet C.𝒰)
      (GM13.ptV Γ u₁.1) (GM13.ptV Γ u₂.1) = W.brickDist u₁ u₂ := by
    have h1 := drawnOnCells_planeWallDist_eq_fig1CellBrickDist hh1 hD le_rfl
      (W.vertCell_mem_fig1WallCells h2 he hW hu₁)
      (W.vertCell_mem_fig1WallCells h2 he hW hu₂)
      (W.val_mem_toGMWall_elemV_vertCell h2 he hW hu₁)
      (W.val_mem_toGMWall_elemV_vertCell h2 he hW hu₂)
      (fun e => hu_ne (Fin.ext e))
    have hbrick : W.brickDist u₁ u₂ = fig1CellBrickDist h (W.vertCell u₁) (W.vertCell u₂) := by
      simp [brickDist, hu_ne]
    rw [h1, hH_height, ← hbrick]
  have hdist_u' : d - 4 ≤ GM13.planeWallDist (GM13.indU Γ W'_gm)
      (GM13.ptV Γ u₁.1) (GM13.ptV Γ u₂.1) := by
    rw [hD'.indU_eq]
    omega
  obtain ⟨Q₁_g, hQ₁_g, hVQ₁⟩ :=
    W.exists_isGraphPathWithEnds_toGMWall_of_isWallEdge h2 he hW hne₁ hnd₁ hV₁ hE₁
  obtain ⟨Q₂_g, hQ₂_g, hVQ₂⟩ :=
    W.exists_isGraphPathWithEnds_toGMWall_of_isWallEdge h2 he hW hne₂ hnd₂ hV₂ hE₂
  rw [hhead₁, hlast₁] at hQ₁_g
  rw [hhead₂, hlast₂] at hQ₂_g
  have hX₁_g : V(Q₁_g) ∩ V(W'_gm.graph) ⊆ {w₁.1} := by
    rintro x ⟨hxQ, hxW'⟩
    rw [hVQ₁, Set.mem_ofPred_eq, List.mem_map] at hxQ
    rcases hxQ with ⟨v, hvQ, rfl⟩
    have hvW' : v ∈ (W.realizeSubwall R).vertexFinset :=
      (W.mem_realizeSubwall_vertexFinset_iff_val_mem_realizeWall R h2 he hW hh'1 he' v).mpr hxW'
    exact congrArg Fin.val (hX₁ v hvQ hvW')
  have hX₂_g : V(Q₂_g) ∩ V(W'_gm.graph) ⊆ {w₂.1} := by
    rintro x ⟨hxQ, hxW'⟩
    rw [hVQ₂, Set.mem_ofPred_eq, List.mem_map] at hxQ
    rcases hxQ with ⟨v, hvQ, rfl⟩
    have hvW' : v ∈ (W.realizeSubwall R).vertexFinset :=
      (W.mem_realizeSubwall_vertexFinset_iff_val_mem_realizeWall R h2 he hW hh'1 he' v).mpr hxW'
    exact congrArg Fin.val (hX₂ v hvQ hvW')
  have hdisj_g : Disjoint V(Q₁_g) V(Q₂_g) :=
    GM13.disjoint_of_three_le_planeWallDist (Γ := Γ) hQ₁_g hQ₂_g hle hX₁_g hX₂_g (by omega)
  have hdisj_list : ∀ x, x ∈ Q₁ → x ∈ Q₂ → False := by
    intro x hx₁ hx₂
    have hx₁_g : x.1 ∈ V(Q₁_g) := by
      rw [hVQ₁]; exact List.mem_map_of_mem hx₁
    have hx₂_g : x.1 ∈ V(Q₂_g) := by
      rw [hVQ₂]; exact List.mem_map_of_mem hx₂
    exact Set.disjoint_left.mp hdisj_g hx₁_g hx₂_g
  refine ⟨hdisj_list, ?_⟩
  have hw_ne : w₁ ≠ w₂ := fun e =>
    hdisj_list w₁ (hlast₁ ▸ List.getLast_mem hne₁) (e ▸ hlast₂ ▸ List.getLast_mem hne₂)
  have hw₁_g : w₁.1 ∈ V(W'_gm.graph) :=
    (W.mem_realizeSubwall_vertexFinset_iff_val_mem_realizeWall R h2 he hW hh'1 he' w₁).mp hw₁
  have hw₂_g : w₂.1 ∈ V(W'_gm.graph) :=
    (W.mem_realizeSubwall_vertexFinset_iff_val_mem_realizeWall R h2 he hW hh'1 he' w₂).mp hw₂
  have hpaths_le := GM13.planeWallDist_le_of_paths hQ₁_g hQ₂_g hle hw₁_g hw₂_g hX₁_g hX₂_g
    hdisj_g C'.naming.not_square hD'.indU_eq
  have hW'_valid : (W.realizeSubwall R).IsValid := W.realizeSubwall_isValid R hW
  have hdist_w' : GM13.planeWallDist (GM13.indU Γ W'_gm) (GM13.ptV Γ w₁.1) (GM13.ptV Γ w₂.1) =
      (W.realizeSubwall R).brickDist w₁ w₂ := by
    have h2_eq := drawnOnCells_planeWallDist_eq_fig1CellBrickDist hh'1 hD' hle
      ((W.realizeSubwall R).vertCell_mem_fig1WallCells h2' he' hW'_valid hw₁)
      ((W.realizeSubwall R).vertCell_mem_fig1WallCells h2' he' hW'_valid hw₂)
      (W.val_mem_realizeWall_elemV_vertCell R h2 he hW hh'1 he' hw₁)
      (W.val_mem_realizeWall_elemV_vertCell R h2 he hW hh'1 he' hw₂)
      (fun e => hw_ne (Fin.ext e))
    have hbrick : (W.realizeSubwall R).brickDist w₁ w₂ =
        fig1CellBrickDist h' ((W.realizeSubwall R).vertCell w₁) ((W.realizeSubwall R).vertCell w₂) := by
      simp [brickDist, hw_ne]
    rw [hD'.indU_eq, h2_eq, hW'_height, ← hbrick]
  omega


/-! ### Section 4: Pre-Star Rays (`IsPreStarRay`) and Extending a Star Ray (`extendStarRay`) -/

/-- A pre-star ray over `W` with center `c`: identical to `W.IsStarRay c P` except that `P` may have
length `1` (`[c]`) when `c ∈ W.vertexFinset`. Once `c ∉ W.vertexFinset`, `IsPreStarRay` is
equivalent to `IsStarRay`. -/
def IsPreStarRay (c : Fin n) (P : List (Fin n)) : Prop :=
  ∃ hne : P ≠ [],
    P.head hne = c ∧
    P.Nodup ∧
    IsSimpleWalkList G P ∧
    P.getLast hne ∈ W.vertexFinset ∧
    (∀ v ∈ (P.drop 1).dropLast, v ∉ W.vertexFinset) ∧
    (∀ u v, (u, v) ∈ P.zip (P.drop 1) → ¬ W.IsWallEdge u v)

theorem IsStarRay.toPreStarRay {c : Fin n} {P : List (Fin n)} (hP : W.IsStarRay c P) :
    W.IsPreStarRay c P := by
  obtain ⟨hne, hhead, _, hnd, hw, hlast, hint, hedge⟩ := hP
  exact ⟨hne, hhead, hnd, hw, hlast, hint, hedge⟩

theorem IsPreStarRay.toStarRay {c : Fin n} {P : List (Fin n)} (hP : W.IsPreStarRay c P)
    (hc : c ∉ W.vertexFinset) :
    W.IsStarRay c P := by
  obtain ⟨hne, hhead, hnd, hw, hlast, hint, hedge⟩ := hP
  refine ⟨hne, hhead, ?_, hnd, hw, hlast, hint, hedge⟩
  cases P with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [List.head_cons] at hhead
      simp only [List.getLast_singleton] at hlast
      subst hhead
      exact False.elim (hc hlast)
    | cons y ys =>
      simp

theorem mem_cases_head_or_drop_dropLast_or_getLast {α : Type*} :
    ∀ {P : List α} (hne : P ≠ []) {v : α},
      v ∈ P → v = P.head hne ∨ v ∈ (P.drop 1).dropLast ∨ v = P.getLast hne
  | [], hne, _, _ => False.elim (hne rfl)
  | [x], _, v, hv => by
    simp only [List.mem_singleton] at hv
    exact Or.inl hv
  | x :: y :: rest, _, v, hv => by
    rcases List.mem_cons.mp hv with rfl | htail
    · exact Or.inl rfl
    · have hne' : y :: rest ≠ [] := List.cons_ne_nil y rest
      have happ : (y :: rest).dropLast ++ [(y :: rest).getLast hne'] = y :: rest :=
        List.dropLast_append_getLast hne'
      rw [← happ, List.mem_append, List.mem_singleton] at htail
      rcases htail with hdrop | hlast
      · exact Or.inr (Or.inl hdrop)
      · exact Or.inr (Or.inr hlast)

theorem IsPreStarRay.eq_center_or_getLast_of_mem_vertexFinset {c : Fin n} {P : List (Fin n)}
    (hP : W.IsPreStarRay c P) {v : Fin n} (hvP : v ∈ P) (hvW : v ∈ W.vertexFinset) :
    ∃ hne : P ≠ [], v = c ∨ v = P.getLast hne := by
  obtain ⟨hne, hhead, _, _, _, hint, _⟩ := hP
  refine ⟨hne, ?_⟩
  rcases mem_cases_head_or_drop_dropLast_or_getLast hne hvP with h1 | h2 | h3
  · exact Or.inl (h1.trans hhead)
  · exact False.elim (hint v h2 hvW)
  · exact Or.inr h3

theorem not_getLast_mem_dropLast_of_nodup {α : Type*} :
    ∀ {P : List α} (hne : P ≠ []), P.Nodup → P.getLast hne ∉ P.dropLast
  | [], hne, _ => False.elim (hne rfl)
  | [_], _, _ => by simp
  | x :: y :: rest, _, hnd => by
    have hne' : y :: rest ≠ [] := List.cons_ne_nil y rest
    rw [List.dropLast_cons_of_ne_nil hne', List.getLast_cons hne', List.mem_cons]
    rintro (rfl | hmem)
    · exact (List.nodup_cons.mp hnd).1 (List.getLast_mem hne')
    · exact not_getLast_mem_dropLast_of_nodup hne' (List.nodup_cons.mp hnd).2 hmem

theorem IsPreStarRay.eq_center_of_mem_dropLast_of_mem_vertexFinset {c : Fin n} {P : List (Fin n)}
    (hP : W.IsPreStarRay c P) {v : Fin n} (hvP : v ∈ P.dropLast) (hvW : v ∈ W.vertexFinset) :
    v = c := by
  obtain ⟨hne, hhead, hnd, _, _, hint, _⟩ := hP
  have hv_mem : v ∈ P := List.dropLast_subset P hvP
  rcases mem_cases_head_or_drop_dropLast_or_getLast hne hv_mem with h1 | h2 | h3
  · exact h1.trans hhead
  · exact False.elim (hint v h2 hvW)
  · subst h3
    exact False.elim (not_getLast_mem_dropLast_of_nodup hne hnd hvP)

theorem ne_head_and_ne_getLast_of_mem_drop_dropLast_of_nodup {α : Type*} :
    ∀ {P : List α} (hne : P ≠ []), P.Nodup →
      ∀ v ∈ (P.drop 1).dropLast, v ≠ P.head hne ∧ v ≠ P.getLast hne
  | [], hne, _, _, _ => False.elim (hne rfl)
  | [_], _, _, _, hv => by simp at hv
  | x :: y :: rest, _, hnd, v, hv => by
    have hne' : y :: rest ≠ [] := List.cons_ne_nil y rest
    simp only [List.drop_succ_cons, List.drop_zero] at hv
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact (List.nodup_cons.mp hnd).1 (List.dropLast_subset (y :: rest) hv)
    · rw [List.getLast_cons hne']
      rintro rfl
      exact not_getLast_mem_dropLast_of_nodup hne' (List.nodup_cons.mp hnd).2 hv

theorem ne_of_mem_zip_of_nodup {α : Type*} :
    ∀ {P : List α}, P.Nodup → ∀ a b, (a, b) ∈ P.zip (P.drop 1) → a ≠ b
  | [], _, _, _, hab => by nomatch hab
  | [_], _, _, _, hab => by nomatch hab
  | x :: y :: rest, hnd, a, b, hab => by
    rcases List.mem_cons.mp hab with ⟨rfl, rfl⟩ | htail
    · rintro rfl
      exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
    · exact ne_of_mem_zip_of_nodup (List.nodup_cons.mp hnd).2 a b htail

theorem mem_zip_concat_overlap {α : Type*} :
    ∀ {L₁ L₂ : List α} (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ []),
      L₁.getLast hne₁ = L₂.head hne₂ →
      ∀ {u v : α}, (u, v) ∈ (L₁.dropLast ++ L₂).zip ((L₁.dropLast ++ L₂).drop 1) →
        (u, v) ∈ L₁.zip (L₁.drop 1) ∨ (u, v) ∈ L₂.zip (L₂.drop 1)
  | [], _, hne₁, _, _, _, _, _ => False.elim (hne₁ rfl)
  | [x], L₂, _, _, _, u, v, huv => Or.inr (by simpa using huv)
  | [x, y], L₂, _, hne₂, heq, u, v, huv => by
    rcases List.exists_cons_of_ne_nil hne₂ with ⟨z, zs, hL₂⟩
    have hyz : y = z := by
      simpa [hL₂] using heq
    subst hyz
    have huv' : (u, v) = (x, y) ∨ (u, v) ∈ (y :: zs).zip zs := by
      simpa [hL₂] using huv
    rcases huv' with ⟨rfl, rfl⟩ | htail
    · exact Or.inl List.mem_cons_self
    · exact Or.inr (by simpa [hL₂] using htail)
  | x :: y :: z :: xs, L₂, _, hne₂, heq, u, v, huv => by
    rcases List.mem_cons.mp huv with ⟨rfl, rfl⟩ | htail
    · exact Or.inl List.mem_cons_self
    · rcases mem_zip_concat_overlap (List.cons_ne_nil y (z :: xs)) hne₂ heq htail with h1 | h2
      · exact Or.inl (List.mem_cons_of_mem (x, y) h1)
      · exact Or.inr h2

end WallOfHeight

/-- Extend a star ray `P` (with center `c` and endpoint `u`) by a path `Q` in `W` from `u` to `w`,
following `GM13.exists_new_leg` (Section 7, page 92, Claim (1)). -/
def extendStarRay {n : ℕ} (c : Fin n) (P Q : List (Fin n)) : List (Fin n) :=
  if c ∈ Q then
    suffixFrom c Q
  else
    P.dropLast ++ Q

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

theorem extendStarRay_props {h' : ℕ} {W' : WallOfHeight h' G}
    (hV_sub : W'.vertexFinset ⊆ W.vertexFinset)
    (hE_sub : ∀ a b, W'.IsWallEdge a b → W.IsWallEdge a b)
    {c u w : Fin n} {P Q : List (Fin n)}
    (hP : W.IsPreStarRay c P)
    (hlastP : ∀ hne : P ≠ [], P.getLast hne = u)
    (hneQ : Q ≠ []) (hheadQ : Q.head hneQ = u) (hlastQ : Q.getLast hneQ = w)
    (hw : w ∈ W'.vertexFinset)
    (hXQ : ∀ x ∈ Q, x ∈ W'.vertexFinset → x = w)
    (hndQ : Q.Nodup) (hwQ : IsSimpleWalkList G Q)
    (hVQ : ∀ x ∈ Q, x ∈ W.vertexFinset) :
    let R := extendStarRay c P Q
    ∃ hneR : R ≠ [],
      W'.IsPreStarRay c R ∧
      R.getLast hneR = w ∧
      (∀ x ∈ R, x ∈ P ∨ x ∈ Q) := by
  obtain ⟨hneP, hheadP, hndP, hwP, _, hintP, hedgeP⟩ := hP
  have hlastP' : P.getLast hneP = u := hlastP hneP
  have hQ_no_W'_edge : ∀ a b, (a, b) ∈ Q.zip (Q.drop 1) → ¬ W'.IsWallEdge a b := by
    intro a b hab hedge'
    obtain ⟨haW', hbW'⟩ := W'.mem_vertexFinset_of_isWallEdge hedge'
    have haQ : a ∈ Q := (List.of_mem_zip hab).1
    have hbQ : b ∈ Q := List.mem_of_mem_drop (List.of_mem_zip hab).2
    have haw : a = w := hXQ a haQ haW'
    have hbw : b = w := hXQ b hbQ hbW'
    exact ne_of_mem_zip_of_nodup hndQ a b hab (haw.trans hbw.symm)
  dsimp only [extendStarRay]
  split_ifs with hcQ
  · have hneR : suffixFrom c Q ≠ [] := suffixFrom_ne_nil hcQ
    have hheadR : (suffixFrom c Q).head hneR = c := head_suffixFrom hcQ
    have hlastR : (suffixFrom c Q).getLast hneR = w :=
      (getLast_suffixFrom hcQ hneQ).trans hlastQ
    have hndR : (suffixFrom c Q).Nodup := nodup_suffixFrom hndQ
    have hwR : IsSimpleWalkList G (suffixFrom c Q) := isSimpleWalkList_suffixFrom hwQ
    refine ⟨hneR, ⟨hneR, hheadR, hndR, hwR, hlastR ▸ hw, ?_, ?_⟩, hlastR,
      fun x hx => Or.inr (mem_of_mem_suffixFrom hx)⟩
    · intro v hv hvW'
      have hne_last := (ne_head_and_ne_getLast_of_mem_drop_dropLast_of_nodup hneR hndR v hv).2
      rw [hlastR] at hne_last
      have hvQ : v ∈ Q :=
        mem_of_mem_suffixFrom (List.mem_of_mem_drop (List.dropLast_subset _ hv))
      exact hne_last (hXQ v hvQ hvW')
    · intro a b hab
      exact hQ_no_W'_edge a b (mem_zip_of_mem_zip_suffixFrom hab)
  · have hneR : P.dropLast ++ Q ≠ [] := List.append_ne_nil_of_right_ne_nil _ hneQ
    have hdrop_ne : P.dropLast ≠ [] := by
      intro hnil
      have hlen : P.length = 1 := by
        cases P with
        | nil => exact False.elim (hneP rfl)
        | cons x xs =>
          cases xs with
          | nil => rfl
          | cons y ys => simp at hnil
      have hcu : c = u := by
        cases P with
        | nil => exact False.elim (hneP rfl)
        | cons x xs =>
          cases xs with
          | nil =>
            simp only [List.head_cons] at hheadP
            simp only [List.getLast_singleton] at hlastP'
            exact hheadP.symm.trans hlastP'
          | cons y ys => simp at hlen
      rw [hcu, ← hheadQ] at hcQ
      exact hcQ (List.head_mem hneQ)
    have hheadR : (P.dropLast ++ Q).head hneR = c := by
      rw [List.head_append_of_ne_nil hdrop_ne, List.head_dropLast hdrop_ne, hheadP]
    have hlastR : (P.dropLast ++ Q).getLast hneR = w := by
      rw [List.getLast_append_of_ne_nil _ hneQ, hlastQ]
    have hndR : (P.dropLast ++ Q).Nodup := by
      have hnd_drop : P.dropLast.Nodup := by
        have h1 : P.dropLast ++ [P.getLast hneP] = P := List.dropLast_append_getLast hneP
        have hnd' := h1 ▸ hndP
        exact hnd'.of_append_left
      refine hnd_drop.append hndQ ?_
      intro v hv₁ hv₂
      have hvW : v ∈ W.vertexFinset := hVQ v hv₂
      have hvc : v = c :=
        IsPreStarRay.eq_center_of_mem_dropLast_of_mem_vertexFinset W
          ⟨hneP, hheadP, hndP, hwP, hlastP' ▸ hVQ u (hheadQ ▸ List.head_mem hneQ), hintP, hedgeP⟩
          hv₁ hvW
      exact hcQ (hvc ▸ hv₂)
    have hwR : IsSimpleWalkList G (P.dropLast ++ Q) :=
      isSimpleWalkList_concat_overlap hneP hneQ hwP hwQ (hlastP'.trans hheadQ.symm)
    refine ⟨hneR, ⟨hneR, hheadR, hndR, hwR, hlastR ▸ hw, ?_, ?_⟩, hlastR,
      fun x hx => (List.mem_append.mp hx).imp (fun h => List.dropLast_subset P h) id⟩
    · intro v hv hvW'
      obtain ⟨hne_c, hne_w⟩ := ne_head_and_ne_getLast_of_mem_drop_dropLast_of_nodup hneR hndR v hv
      rw [hheadR] at hne_c
      rw [hlastR] at hne_w
      have hv_mem : v ∈ P.dropLast ++ Q :=
        List.mem_of_mem_drop (List.dropLast_subset _ hv)
      rcases List.mem_append.mp hv_mem with hvP | hvQ
      · have hvc := IsPreStarRay.eq_center_of_mem_dropLast_of_mem_vertexFinset W
          ⟨hneP, hheadP, hndP, hwP, hlastP' ▸ hVQ u (hheadQ ▸ List.head_mem hneQ), hintP, hedgeP⟩
          hvP (hV_sub hvW')
        exact hne_c hvc
      · exact hne_w (hXQ v hvQ hvW')
    · intro a b hab hedge'
      rcases mem_zip_concat_overlap hneP hneQ (hlastP'.trans hheadQ.symm) hab with habP | habQ
      · exact hedgeP a b habP (hE_sub a b hedge')
      · exact hQ_no_W'_edge a b habQ hedge'

end WallOfHeight


/-! ### Section 5: One Step and `k`-Step Iteration of (7.6) (`step76One`, `step76Iter`) -/

/-- State at step `s` of (7.6) (`0 ≤ s ≤ k`): a wall `W : WallOfHeight h G` and `k` families of `l`
star rays over `W`. -/
structure Step76State (h k l : ℕ) {n : ℕ} (G : MultiDigraph n) where
  /-- Current wall of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- Current rays of each of the `k` stars. -/
  rays : Fin k → Fin l → List (Fin n)

namespace Step76State

variable {h k l n : ℕ} {G : MultiDigraph n}

/-- Validity invariant of a `Step76State` with current distance bound `d` and avoided center
predicate `P_avoid : Fin k → Prop`. -/
def IsValid (centers : Fin k → Fin n) (d : ℕ) (P_avoid : Fin k → Prop)
    (st : Step76State h k l G) : Prop :=
  (2 ≤ h ∧ Even h ∧ st.W.IsValid) ∧
  (∀ a : Fin k, P_avoid a → centers a ∉ st.W.vertexFinset) ∧
  (∀ a : Fin k, ∀ i : Fin l, st.W.IsPreStarRay (centers a) (st.rays a i)) ∧
  (∀ a : Fin k, ∀ i j : Fin l, i ≠ j → ∀ v, v ∈ st.rays a i → v ∈ st.rays a j → v = centers a) ∧
  (∀ a : Fin k, ∀ i j : Fin l, i ≠ j → ∀ u v,
    (st.rays a i).getLast? = some u → (st.rays a j).getLast? = some v → d ≤ st.W.brickDist u v)

theorem IsValid.mono_avoid {centers : Fin k → Fin n} {d : ℕ}
    {P₁ P₂ : Fin k → Prop} {st : Step76State h k l G}
    (h : st.IsValid centers d P₁) (himp : ∀ a, P₂ a → P₁ a) :
    st.IsValid centers d P₂ :=
  ⟨h.1, fun a ha => h.2.1 a (himp a ha), h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Initial state of (7.6) from an `Alg77Input`. -/
def ofAlg77Input {p m : ℕ} (x : Alg77Input p l m) : Step76State x.h (p.choose 2) l x.G where
  W := x.W
  rays := x.rays

theorem isValid_ofAlg77Input {p m : ℕ} (x : Alg77Input p l m) :
    (ofAlg77Input x).IsValid x.centers m (fun _ => False) := by
  refine ⟨x.hW_valid, fun _ ha => False.elim ha, fun a i => (x.hrays a i).toPreStarRay,
    x.hrays_meet, x.hends_dist⟩

attribute [local irreducible]
  WallOfHeight.step73DeletingRealization
  WallOfHeight.pathToSubwall
  extendStarRay

/-- One step of (7.6) on `st : Step76State (h' + 2) k l G`: apply (7.3) with `r = 0` to remove
`v_del` from `st.W`, and extend every ray of every star by a minimal path in `st.W` to the new
wall `W'`. -/
def stepOneAux {h' : ℕ} (st : Step76State (h' + 2) k l G) (centers : Fin k → Fin n) (v_del : Fin n)
    (hh' : 1 ≤ h') (he' : Even h') : Step76State h' k l G :=
  let delR := st.W.step73DeletingRealization hh' he' v_del
  let R := delR.R
  let W' := st.W.step73Subwall hh' he' v_del
  let q₀ := R.vmap (1, 0)
  { W := W'
    rays := fun a i =>
      let P := st.rays a i
      let u := P.getLast?.getD (centers a)
      let Q := st.W.pathToSubwall W'.vertexFinset u q₀
      extendStarRay (centers a) P Q }

theorem isValid_stepOneAux {h' : ℕ} {st : Step76State (h' + 2) k l G} {centers : Fin k → Fin n}
    {d : ℕ} {P_avoid : Fin k → Prop} (hst : st.IsValid centers d P_avoid) (a_del : Fin k)
    (hh' : 1 ≤ h') (h2' : 2 ≤ h') (he' : Even h') (hd7 : 7 ≤ d) :
    (st.stepOneAux centers (centers a_del) hh' he').IsValid
      centers (d - 4) (fun a => a = a_del ∨ P_avoid a) := by
  obtain ⟨⟨h2, he, hW⟩, havoid, hrays, hmeet, hdist⟩ := hst
  have hh1 : 1 ≤ h' + 2 := by omega
  let delR := st.W.step73DeletingRealization hh' he' (centers a_del)
  let R := delR.R
  let W' := st.W.step73Subwall hh' he' (centers a_del)
  let q₀ := R.vmap (1, 0)
  have h10_mem : ((1, 0) : ℕ × ℕ) ∈ GM13.elementaryWallVerts h' := by
    simp only [GM13.elementaryWallVerts, Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq]
    omega
  have hq₀_mem : q₀ ∈ GM13.elementaryWallVerts (h' + 2) := R.vmap_mem (1, 0) h10_mem
  have hTarget : st.W.branchVert (elemWallCoordIdx (h' + 2) q₀ hq₀_mem) ∈ W'.vertexFinset := by
    let u₀ : Fin (elemWallNumVerts h') := elemWallCoordIdx h' (1, 0) h10_mem
    have hu₀_coord : elemWallVertCoord h' u₀ = (1, 0) :=
      elemWallVertCoord_elemWallCoordIdx h' h10_mem
    have hbr_eq : W'.branchVert u₀ = st.W.branchVert (elemWallCoordIdx (h' + 2) q₀ hq₀_mem) :=
      congrArg st.W.branchVert
        (WallOfHeight.elemWallCoordIdx_eq_of_eq _ hq₀_mem (congrArg R.vmap hu₀_coord))
    rw [← hbr_eq]
    exact W'.branchVert_mem_vertexFinset u₀
  have hW'_valid : W'.IsValid := st.W.step73Subwall_isValid hh' he' hW (centers a_del)
  have hV_sub : W'.vertexFinset ⊆ st.W.vertexFinset :=
    st.W.step73Subwall_vertexFinset_subset hh' he' hW (centers a_del)
  have hE_sub : ∀ x y, W'.IsWallEdge x y → st.W.IsWallEdge x y :=
    fun x y hxy => st.W.isWallEdge_of_realizeSubwall_isWallEdge R hxy
  have hray_step : ∀ (a : Fin k) (i : Fin l),
      let P := st.rays a i
      let u := P.getLast?.getD (centers a)
      let Q := st.W.pathToSubwall W'.vertexFinset u q₀
      let R_ray := extendStarRay (centers a) P Q
      ∃ (hneP : P ≠ []) (hneQ : Q ≠ []) (hneR : R_ray ≠ []),
        P.getLast hneP = u ∧
        u ∈ st.W.vertexFinset ∧
        Q.head hneQ = u ∧
        Q.getLast hneQ ∈ W'.vertexFinset ∧
        (∀ x ∈ Q, x ∈ W'.vertexFinset → x = Q.getLast hneQ) ∧
        Q.Nodup ∧
        WallOfHeight.IsSimpleWalkList G Q ∧
        (∀ x ∈ Q, x ∈ st.W.vertexFinset) ∧
        (∀ x y, (x, y) ∈ Q.zip (Q.drop 1) → st.W.IsWallEdge x y) ∧
        W'.IsPreStarRay (centers a) R_ray ∧
        R_ray.getLast hneR = Q.getLast hneQ ∧
        (∀ x ∈ R_ray, x ∈ P ∨ x ∈ Q) := by
    intro a i
    dsimp only
    obtain ⟨hneP, _, _, _, hlastP_mem, _, _⟩ := hrays a i
    let P := st.rays a i
    let u := P.getLast?.getD (centers a)
    have hu_eq : P.getLast hneP = u := by
      dsimp only [u]
      rw [List.getLast?_eq_some_getLast hneP, Option.getD_some]
    have hu_mem : u ∈ st.W.vertexFinset := hu_eq ▸ hlastP_mem
    obtain ⟨hneQ, hheadQ, hlastQ_mem, hXQ, hndQ, hwQ, hVQ, hEQ⟩ :=
      st.W.pathToSubwall_props hh1 hW hu_mem hq₀_mem hTarget
    obtain ⟨hneR, hpreR, hlastR, hsubR⟩ :=
      st.W.extendStarRay_props hV_sub hE_sub (hrays a i) (fun _ => hu_eq)
        hneQ hheadQ rfl hlastQ_mem hXQ hndQ hwQ hVQ
    exact ⟨hneP, hneQ, hneR, hu_eq, hu_mem, hheadQ, hlastQ_mem, hXQ, hndQ, hwQ, hVQ, hEQ,
      hpreR, hlastR, hsubR⟩
  have hQ_disj_and_dist : ∀ (a : Fin k) (i j : Fin l), i ≠ j →
      let u_i := (st.rays a i).getLast?.getD (centers a)
      let u_j := (st.rays a j).getLast?.getD (centers a)
      let Q_i := st.W.pathToSubwall W'.vertexFinset u_i q₀
      let Q_j := st.W.pathToSubwall W'.vertexFinset u_j q₀
      ∀ (hneQi : Q_i ≠ []) (hneQj : Q_j ≠ []),
        (∀ x, x ∈ Q_i → x ∈ Q_j → False) ∧
        d - 4 ≤ W'.brickDist (Q_i.getLast hneQi) (Q_j.getLast hneQj) := by
    intro a i j hij
    dsimp only
    obtain ⟨hnePi, _, _, hui_eq, hui_mem, hheadQi, hlastQi_mem, hXQi, hndQi, _, hVQi, hEQi,
      _, _, _⟩ := hray_step a i
    obtain ⟨hnePj, _, _, huj_eq, huj_mem, hheadQj, hlastQj_mem, hXQj, hndQj, _, hVQj, hEQj,
      _, _, _⟩ := hray_step a j
    intro hneQi' hneQj'
    have hdist_ij : d ≤ st.W.brickDist ((st.rays a i).getLast?.getD (centers a))
        ((st.rays a j).getLast?.getD (centers a)) := by
      apply hdist a i j hij
      · rw [List.getLast?_eq_some_getLast hnePi]
        rfl
      · rw [List.getLast?_eq_some_getLast hnePj]
        rfl
    exact st.W.disjoint_and_brickDist_ge_of_paths_to_realizeSubwall h2 he hW h2' he' R delR.hdepth
      hui_mem huj_mem
      hneQi' hheadQi rfl hlastQi_mem hXQi hndQi hVQi hEQi
      hneQj' hheadQj rfl hlastQj_mem hXQj hndQj hVQj hEQj
      hd7 hdist_ij
  refine ⟨⟨h2', he', hW'_valid⟩, ?_, ?_, ?_, ?_⟩
  · rintro a (ha_eq | ha_prev)
    · rw [ha_eq]
      exact st.W.not_mem_step73Subwall_vertexFinset hh' he' hW (centers a_del)
    · intro hmem
      exact havoid a ha_prev (hV_sub hmem)
  · intro a i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpreR, _, _⟩ := hray_step a i
    exact hpreR
  · intro a i j hij v hvi hvj
    obtain ⟨_, hneQi, _, hui_eq, _, hheadQi, _, _, _, _, hVQi, _, _, _, hsubRi⟩ :=
      hray_step a i
    obtain ⟨_, hneQj, _, huj_eq, _, hheadQj, _, _, _, _, hVQj, _, _, _, hsubRj⟩ :=
      hray_step a j
    have hdisj := (hQ_disj_and_dist a i j hij hneQi hneQj).1
    rcases hsubRi v hvi with hvPi | hvQi <;> rcases hsubRj v hvj with hvPj | hvQj
    · exact hmeet a i j hij v hvPi hvPj
    · obtain ⟨_, hvc | hvu⟩ :=
        WallOfHeight.IsPreStarRay.eq_center_or_getLast_of_mem_vertexFinset st.W (hrays a i)
          hvPi (hVQj v hvQj)
      · exact hvc
      · rw [hui_eq, ← hheadQi] at hvu
        exact False.elim (hdisj v (hvu ▸ List.head_mem hneQi) hvQj)
    · obtain ⟨_, hvc | hvu⟩ :=
        WallOfHeight.IsPreStarRay.eq_center_or_getLast_of_mem_vertexFinset st.W (hrays a j)
          hvPj (hVQi v hvQi)
      · exact hvc
      · rw [huj_eq, ← hheadQj] at hvu
        exact False.elim (hdisj v hvQi (hvu ▸ List.head_mem hneQj))
    · exact False.elim (hdisj v hvQi hvQj)
  · intro a i j hij w₁ w₂ hw₁ hw₂
    obtain ⟨_, hneQi, hneRi, _, _, _, _, _, _, _, _, _, _, hlastRi, _⟩ := hray_step a i
    obtain ⟨_, hneQj, hneRj, _, _, _, _, _, _, _, _, _, _, hlastRj, _⟩ := hray_step a j
    have hw₁_eq : w₁ = (st.W.pathToSubwall W'.vertexFinset
        ((st.rays a i).getLast?.getD (centers a)) q₀).getLast hneQi := by
      dsimp only [stepOneAux] at hw₁
      rw [List.getLast?_eq_some_getLast hneRi, Option.some.injEq] at hw₁
      exact hw₁.symm.trans hlastRi
    have hw₂_eq : w₂ = (st.W.pathToSubwall W'.vertexFinset
        ((st.rays a j).getLast?.getD (centers a)) q₀).getLast hneQj := by
      dsimp only [stepOneAux] at hw₂
      rw [List.getLast?_eq_some_getLast hneRj, Option.some.injEq] at hw₂
      exact hw₂.symm.trans hlastRj
    rw [hw₁_eq, hw₂_eq]
    exact (hQ_disj_and_dist a i j hij hneQi hneQj).2

/-- One step of (7.6) on `st : Step76State h k l G` (`4 ≤ h`, `Even h`). -/
def stepOne (st : Step76State h k l G) (centers : Fin k → Fin n) (v_del : Fin n)
    (hh : 4 ≤ h) (he : Even h) : Step76State (h - 2) k l G :=
  have hh' : 1 ≤ h - 2 := by omega
  have he' : Even (h - 2) := by
    obtain ⟨t, ht⟩ := he
    exact ⟨t - 1, by omega⟩
  have heq : h = (h - 2) + 2 := by omega
  (cast (by rw [← heq]) st : Step76State ((h - 2) + 2) k l G).stepOneAux centers v_del hh' he'

theorem isValid_stepOne {st : Step76State h k l G} {centers : Fin k → Fin n}
    {d : ℕ} {P_avoid : Fin k → Prop} (hst : st.IsValid centers d P_avoid) (a_del : Fin k)
    (hh : 4 ≤ h) (hd7 : 7 ≤ d) :
    (st.stepOne centers (centers a_del) hh hst.1.2.1).IsValid
      centers (d - 4) (fun a => a = a_del ∨ P_avoid a) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
  have he' : Even h' := by
    obtain ⟨t, ht⟩ := hst.1.2.1
    exact ⟨t - 1, by omega⟩
  exact isValid_stepOneAux hst a_del (by omega) (by omega) he' hd7

/-- Iterate `stepOne` `t` times starting from step index `s` along center sequence `f : ℕ → Fin k`. -/
def stepIter (centers : Fin k → Fin n) (f : ℕ → Fin k) :
    ∀ (t _s : ℕ) {h : ℕ},
      Step76State h k l G →
      2 * t + 2 ≤ h →
      Even h →
      Step76State (h - 2 * t) k l G
  | 0, _, _, st, _, _ => st
  | t + 1, s, h, st, hh, he =>
    have hh4 : 4 ≤ h := by omega
    have he' : Even (h - 2) := by
      obtain ⟨m, hm⟩ := he
      exact ⟨m - 1, by omega⟩
    let st₁ := st.stepOne centers (centers (f s)) hh4 he
    let st₂ := stepIter centers f t (s + 1) st₁ (by omega) he'
    cast (by congr 1; omega) st₂

theorem isValid_cast {h₁ h₂ : ℕ} (h_eq : h₁ = h₂) {centers : Fin k → Fin n} {d : ℕ}
    {P_avoid : Fin k → Prop} {st : Step76State h₁ k l G}
    (hvalid : st.IsValid centers d P_avoid) :
    (cast (by rw [h_eq]) st : Step76State h₂ k l G).IsValid centers d P_avoid := by
  subst h_eq
  exact hvalid

theorem isValid_stepIter (centers : Fin k → Fin n) (f : ℕ → Fin k) :
    ∀ (t s : ℕ) {h d : ℕ} {P_avoid : Fin k → Prop} (st : Step76State h k l G)
      (hh : 2 * t + 2 ≤ h) (he : Even h)
      (_hd : 3 + 4 * t ≤ d) (_hvalid : st.IsValid centers d P_avoid),
      (stepIter centers f t s st hh he).IsValid centers (d - 4 * t)
        (fun a => (∃ i < t, a = f (s + i)) ∨ P_avoid a)
  | 0, s, h, d, P_avoid, st, _, _, _, hvalid => by
    dsimp [stepIter]
    exact hvalid.mono_avoid fun a ha => by
      rcases ha with ⟨i, hi, _⟩ | hp
      · omega
      · exact hp
  | t + 1, s, h, d, P_avoid, st, hh, he, hd, hvalid => by
    have hh4 : 4 ≤ h := by omega
    have he' : Even (h - 2) := by
      obtain ⟨m, hm⟩ := he
      exact ⟨m - 1, by omega⟩
    have hvalid₁ : (st.stepOne centers (centers (f s)) hh4 he).IsValid
        centers (d - 4) (fun a => a = f s ∨ P_avoid a) :=
      isValid_stepOne hvalid (f s) hh4 (by omega)
    have ih := isValid_stepIter centers f t (s + 1)
      (st.stepOne centers (centers (f s)) hh4 he)
      (by omega) he' (by omega) hvalid₁
    have ih' : (stepIter centers f t (s + 1)
        (st.stepOne centers (centers (f s)) hh4 he) (by omega) he').IsValid
        centers (d - 4 * (t + 1))
        (fun a => (∃ i < t + 1, a = f (s + i)) ∨ P_avoid a) := by
      have hd_eq : d - 4 - 4 * t = d - 4 * (t + 1) := by omega
      rw [hd_eq] at ih
      refine ih.mono_avoid fun a ha => ?_
      rcases ha with ⟨i, hi, rfl⟩ | hp
      · cases i with
        | zero =>
          rw [Nat.add_zero]
          exact Or.inr (Or.inl rfl)
        | succ j =>
          refine Or.inl ⟨j, by omega, ?_⟩
          congr 1
          omega
      · exact Or.inr (Or.inr hp)
    exact isValid_cast (by omega) ih'

end Step76State

/-- Given `x : Alg77Input p l (m + 4 * p.choose 2)` with `2 ≤ p`, `3 ≤ l`, `3 ≤ m`, the wall height
satisfies `2 * p.choose 2 + 2 ≤ x.h`. -/
theorem alg77Input_height_ge {p l m : ℕ} (hp : 2 ≤ p) (hl : 3 ≤ l) (hm : 3 ≤ m)
    (x : Alg77Input p l (m + 4 * p.choose 2)) :
    2 * p.choose 2 + 2 ≤ x.h := by
  have hk_pos : 0 < p.choose 2 := Nat.choose_pos hp
  let a₀ : Fin (p.choose 2) := ⟨0, hk_pos⟩
  let i₀ : Fin l := ⟨0, by omega⟩
  let i₁ : Fin l := ⟨1, by omega⟩
  have hne_i : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨hne0, _, _, _, _, hu0_mem, _, _⟩ := x.hrays a₀ i₀
  obtain ⟨hne1, _, _, _, _, hu1_mem, _, _⟩ := x.hrays a₀ i₁
  let u₀ := (x.rays a₀ i₀).getLast hne0
  let u₁ := (x.rays a₀ i₁).getLast hne1
  have hdist_ge : m + 4 * p.choose 2 ≤ x.W.brickDist u₀ u₁ :=
    x.hends_dist a₀ i₀ i₁ hne_i u₀ u₁
      (List.getLast?_eq_some_getLast hne0) (List.getLast?_eq_some_getLast hne1)
  have hdist_le : x.W.brickDist u₀ u₁ ≤ 2 * x.h + 2 :=
    x.W.brickDist_le_two_mul_height_add_two x.hW_valid.1 x.hW_valid.2.1 x.hW_valid.2.2
      hu0_mem hu1_mem
  obtain ⟨t, ht⟩ := x.hW_valid.2.1
  omega

/-- Run all `k = p.choose 2` steps of (7.6) on `x : Alg77Input p l (m + 4 * p.choose 2)`. -/
def runStep76 {p l m : ℕ} (hp : 2 ≤ p) (hl : 3 ≤ l) (hm : 3 ≤ m)
    (x : Alg77Input p l (m + 4 * p.choose 2)) :
    Step76State (x.h - 2 * p.choose 2) (p.choose 2) l x.G :=
  Step76State.stepIter x.centers
    (fun s => ⟨s % p.choose 2, Nat.mod_lt s (Nat.choose_pos hp)⟩)
    (p.choose 2) 0 (Step76State.ofAlg77Input x)
    (alg77Input_height_ge hp hl hm x) x.hW_valid.2.1

/-- Correctness of `runStep76`: produces a valid subwall `W'` of height `x.h - 2 * p.choose 2`
and `p.choose 2` external `(l, m)`-stars (`W'.IsStarRay`) with centers `x.centers a ∉ W'.vertexFinset`. -/
theorem runStep76_spec {p l m : ℕ} (hp : 2 ≤ p) (hl : 3 ≤ l) (hm : 3 ≤ m)
    (x : Alg77Input p l (m + 4 * p.choose 2)) :
    let st := runStep76 hp hl hm x
    (2 ≤ x.h - 2 * p.choose 2 ∧ Even (x.h - 2 * p.choose 2) ∧ st.W.IsValid) ∧
    (∀ a : Fin (p.choose 2), x.centers a ∉ st.W.vertexFinset) ∧
    (∀ a : Fin (p.choose 2), ∀ i : Fin l, st.W.IsStarRay (x.centers a) (st.rays a i)) ∧
    (∀ a : Fin (p.choose 2), ∀ i j : Fin l, i ≠ j →
      ∀ v, v ∈ st.rays a i → v ∈ st.rays a j → v = x.centers a) ∧
    (∀ a : Fin (p.choose 2), ∀ i j : Fin l, i ≠ j → ∀ u v,
      (st.rays a i).getLast? = some u → (st.rays a j).getLast? = some v →
        m ≤ st.W.brickDist u v) := by
  have hvalid := Step76State.isValid_stepIter x.centers
    (fun s => ⟨s % p.choose 2, Nat.mod_lt s (Nat.choose_pos hp)⟩)
    (p.choose 2) 0 (Step76State.ofAlg77Input x)
    (alg77Input_height_ge hp hl hm x) x.hW_valid.2.1
    (by omega) (Step76State.isValid_ofAlg77Input x)
  have hd_eq : m + 4 * p.choose 2 - 4 * p.choose 2 = m := by omega
  rw [hd_eq] at hvalid
  obtain ⟨hW', havoid, hpre, hmeet, hdist⟩ := hvalid
  have havoid_all : ∀ a : Fin (p.choose 2), x.centers a ∉ (runStep76 hp hl hm x).W.vertexFinset := by
    intro a
    refine havoid a (Or.inl ⟨a.1, a.2, ?_⟩)
    ext
    simp [Nat.mod_eq_of_lt a.2]
  exact ⟨hW', havoid_all,
    fun a i => WallOfHeight.IsPreStarRay.toStarRay _ (hpre a i) (havoid_all a),
    hmeet, hdist⟩

end GraphMinor.Compute

