module

public import GraphMinor.Compute.GM06Alg34Singleton

/-!
# Finding a supplied singleton block

A nonempty list represents a singleton exactly when every entry equals
its first entry. This also detects singleton blocks whose labels repeat.
Scan the supplied division lists for the first such block. The finite
search returns a singleton label exactly when one is present, so it can
select reduction (3.3)(i) without any proof-based choice.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a singleton label from a block, allowing repeated copies of it. -/
def gm06SingletonLabel {α : Type*} [DecidableEq α] : List α → Option α
  | [] => none
  | v :: vs => if vs.all (fun a => a == v) then some v else none

/-- Find the first supplied block representing a singleton. -/
def gm06FindSingleton {α : Type*} [DecidableEq α] : List (List α) → Option α
  | [] => none
  | B :: D => (gm06SingletonLabel B).or (gm06FindSingleton D)

/-- Singleton detection commutes with injective changes of the supplied labels. -/
theorem gm06SingletonLabel_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (B : List α) :
    gm06SingletonLabel (B.map f) = (gm06SingletonLabel B).map f := by
  cases B with
  | nil => rfl
  | cons a B =>
    have hall : (B.map f).all (fun b => b == f a) = B.all (fun b => b == a) := by
      simp only [List.all_map]
      congr 1
      funext b
      change (f b == f a) = (b == a)
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact hf.eq_iff
    simp only [List.map_cons, gm06SingletonLabel, hall]
    split <;> rfl

/-- The first-singleton search also commutes with injective label changes. -/
theorem gm06FindSingleton_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (D : List (List α)) :
    gm06FindSingleton (D.map (List.map f)) = (gm06FindSingleton D).map f := by
  induction D with
  | nil => rfl
  | cons B D ih =>
    simp only [List.map_cons, gm06FindSingleton, gm06SingletonLabel_map f hf, ih]
    cases gm06SingletonLabel B <;> rfl

/-- The local list test returns exactly the label of a represented singleton. -/
theorem gm06SingletonLabel_eq_some_iff {n : ℕ} (B : List (Fin n)) (v : Fin n) :
    gm06SingletonLabel B = some v ↔ GM06DrawingData.block B = {v} := by
  cases B with
  | nil =>
    constructor
    · intro h; cases h
    · intro heq
      have hv : v ∈ GM06DrawingData.block ([] : List (Fin n)) := heq.symm ▸ Set.mem_singleton v
      exact False.elim (List.not_mem_nil hv)
  | cons a B =>
    have htest : B.all (fun b => b == a) = true ↔ ∀ b ∈ B, b = a := by
      simp only [List.all_eq_true, beq_iff_eq]
    have hform : gm06SingletonLabel (a :: B) = some v ↔
        (B.all (fun b => b == a) = true ∧ a = v) := by
      by_cases hall : B.all (fun b => b == a) = true <;>
        simp [gm06SingletonLabel, hall]
    rw [hform]
    constructor
    · rintro ⟨hall, rfl⟩
      ext b
      simp only [GM06DrawingData.block, Set.mem_ofPred_eq, List.mem_cons,
        Set.mem_singleton_iff]
      exact ⟨fun hb => hb.elim id (htest.mp hall b), fun hb => Or.inl hb⟩
    · intro heq
      have ha : a = v := heq.subset List.mem_cons_self
      have hall : ∀ b ∈ B, b = a := by
        intro b hb
        exact (heq.subset (List.mem_cons_of_mem a hb)).trans ha.symm
      exact ⟨htest.mpr hall, ha⟩

/-- A returned label belongs to a singleton block in the supplied division. -/
theorem gm06FindSingleton_sound {n : ℕ} (D : List (List (Fin n))) (v : Fin n)
    (h : gm06FindSingleton D = some v) : {v} ∈ gm06BlockSets D := by
  induction D with
  | nil => cases h
  | cons B D ih =>
    cases hb : gm06SingletonLabel B with
    | none =>
      have hd : gm06FindSingleton D = some v := by simpa [gm06FindSingleton, hb] using h
      obtain ⟨A, hA, heq⟩ := ih hd
      exact ⟨A, List.mem_cons_of_mem B hA, heq⟩
    | some a =>
      have hav : a = v := Option.some.inj (by simpa [gm06FindSingleton, hb] using h)
      subst a
      exact ⟨B, List.mem_cons_self, (gm06SingletonLabel_eq_some_iff B v).mp hb⟩

/-- Failure of the finite search means that no singleton block is present. -/
theorem gm06FindSingleton_eq_none_iff {n : ℕ} (D : List (List (Fin n))) :
    gm06FindSingleton D = none ↔ ∀ v, {v} ∉ gm06BlockSets D := by
  constructor
  · intro h v ⟨B, hB, heq⟩
    have hb := (gm06SingletonLabel_eq_some_iff B v).mpr heq
    induction D with
    | nil => cases hB
    | cons A D ih =>
      have hn : gm06SingletonLabel A = none ∧ gm06FindSingleton D = none := by
        cases ha : gm06SingletonLabel A with
        | none => exact ⟨rfl, by simpa [gm06FindSingleton, ha] using h⟩
        | some a => simp [gm06FindSingleton, ha] at h
      rcases List.mem_cons.mp hB with rfl | hB
      · rw [hb] at hn
        cases hn.1
      · exact ih hn.2 hB
  · intro h
    cases hd : gm06FindSingleton D with
    | none => rfl
    | some v => exact False.elim (h v (gm06FindSingleton_sound D v hd))

end GraphMinor.Compute
