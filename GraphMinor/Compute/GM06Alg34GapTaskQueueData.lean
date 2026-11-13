module

public import GraphMinor.Compute.GM06Alg34GapTaskData

/-!
# Canonical finite component work queues

For each canonical component root, queue the same supplied parent
arrays and that root. The exact target list is the augmented component
list of VI (3.3)(iv). Every record has the same length, so filtering
canonical roots gives an explicit bound on the queue words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Component work records in canonical root order. -/
def gm06GapComponentTasks (x : GM06DrawingData) (R : List (Fin x.regions.length)) :
    List GM06GapComponentTask := x.componentRoots.map (fun a => ⟨x, R, a⟩)

/-- Queue words contributed by canonical roots among the supplied source labels. -/
def gm06GapTaskQueueWords (x : GM06DrawingData) (R : List (Fin x.regions.length))
    (V : List (Fin x.n)) : List ℕ :=
  (V.filter x.isComponentRoot).flatMap (fun a => (⟨x, R, a⟩ : GM06GapComponentTask).words)

/-- All work records for a fixed parent have the same finite size. -/
theorem gm06GapTask_size (x : GM06DrawingData) (R : List (Fin x.regions.length)) (a : Fin x.n) :
    (⟨x, R, a⟩ : GM06GapComponentTask).size = x.size + R.length + 3 := by
  rw [GM06GapComponentTask.size, GM06GapComponentTask.words_length, GM06DrawingData.size]
  change x.n + (x.words.length + R.length + 3) = x.n + x.words.length + R.length + 3
  omega

/-- Materializing the records gives exactly the augmented component input list. -/
theorem gm06GapComponentTasks_targets (x : GM06DrawingData) (R : List (Fin x.regions.length)) :
    (gm06GapComponentTasks x R).map GM06GapComponentTask.target =
      (⟨x, [R]⟩ : GM06GapInput).componentGapInputs := by
  simp only [gm06GapComponentTasks, GM06GapInput.componentGapInputs, List.map_map, Function.comp_def]
  rfl

/-- A complete source scan emits exactly the canonical work records. -/
theorem gm06GapTaskQueueWords_eq_tasks (x : GM06DrawingData) (R : List (Fin x.regions.length)) :
    gm06GapTaskQueueWords x R (List.finRange x.n) =
      (gm06GapComponentTasks x R).flatMap GM06GapComponentTask.words := by
  simp only [gm06GapTaskQueueWords, gm06GapComponentTasks, GM06DrawingData.componentRoots,
    List.flatMap_map]

/-- Splitting a source scan at its first label splits its exact emitted queue words. -/
theorem gm06GapTaskQueueWords_cons (x : GM06DrawingData) (R : List (Fin x.regions.length))
    (a : Fin x.n) (V : List (Fin x.n)) :
    gm06GapTaskQueueWords x R (a :: V) =
      (if x.isComponentRoot a then (⟨x, R, a⟩ : GM06GapComponentTask).words else []) ++
        gm06GapTaskQueueWords x R V := by
  cases hp : x.isComponentRoot a <;>
    simp only [gm06GapTaskQueueWords, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_cons, List.nil_append]

private theorem flatMap_length {α : Type*} (f : α → List ℕ) (n : ℕ)
    (hf : ∀ a, (f a).length = n) (V : List α) : (V.flatMap f).length = V.length * n := by
  induction V with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons a V ih =>
    rw [List.flatMap_cons, List.length_append, hf, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Exact queue length is the number of selected roots times the common record length. -/
theorem gm06GapTaskQueueWords_length (x : GM06DrawingData) (R : List (Fin x.regions.length))
    (V : List (Fin x.n)) :
    (gm06GapTaskQueueWords x R V).length =
      (V.filter x.isComponentRoot).length * (x.words.length + R.length + 3) :=
  flatMap_length _ _ (fun a => GM06GapComponentTask.words_length ⟨x, R, a⟩) _

/-- The queue needs at most one fixed-size record per supplied source label. -/
theorem gm06GapTaskQueueWords_length_le (x : GM06DrawingData) (R : List (Fin x.regions.length))
    (V : List (Fin x.n)) :
    (gm06GapTaskQueueWords x R V).length ≤ V.length * (x.words.length + R.length + 3) := by
  rw [gm06GapTaskQueueWords_length]
  exact Nat.mul_le_mul_right _ (List.length_filter_le _ _)

end GraphMinor.Compute
