module

public import GraphMinor.Compute.Case3StepsPushMultigraph

/-!
# The restored multigraph's ordered encoding

Restoring ambient labels maps the endpoints of each positive-pair record
and copies its multiplicity word. The positive-pair order is unchanged, so
this gives the exact canonical encoding needed by output (b) of XIII (9.9).
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Positive-pair records with restored endpoints and unchanged multiplicities. -/
def case3PushFlatTriples {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (pairs : List (Fin S.card × Fin S.card)) : List ℕ :=
  pairs.flatMap (fun p => [(S.orderEmbOfFin rfl p.1).1, (S.orderEmbOfFin rfl p.2).1, D.edgeMult p.1 p.2])

/-- Restoring endpoints does not change the number of stored pair words. -/
theorem case3PushFlatTriples_length {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (pairs : List (Fin S.card × Fin S.card)) :
    (case3PushFlatTriples S D pairs).length = 3 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [case3PushFlatTriples, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega

/-- Concatenating pair lists concatenates their restored encoding words. -/
theorem case3PushFlatTriples_append {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (a b : List (Fin S.card × Fin S.card)) :
    case3PushFlatTriples S D (a ++ b) = case3PushFlatTriples S D a ++ case3PushFlatTriples S D b := by
  exact List.flatMap_append

/-- Advancing a pair prefix appends the next complete restored record. -/
theorem case3PushFlatTriples_take_succ {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (k : ℕ) (hk : k < D.numActivePairs) :
    case3PushFlatTriples S D (D.activePairsList.take (k + 1)) =
      case3PushFlatTriples S D (D.activePairsList.take k) ++
        [(S.orderEmbOfFin rfl (D.activePairsList[k]).1).1,
          (S.orderEmbOfFin rfl (D.activePairsList[k]).2).1,
          D.edgeMult (D.activePairsList[k]).1 (D.activePairsList[k]).2] := by
  rw [List.take_succ_eq_append_getElem hk, case3PushFlatTriples_append]
  simp only [case3PushFlatTriples, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The restored multigraph's pair list writes the restored records. -/
theorem case3PushFlatTriples_eq {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (pairs : List (Fin S.card × Fin S.card)) :
    MultiDigraph.flatTriples (case3PushMultigraph S D)
      (pairs.map (Prod.map (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl))) =
        case3PushFlatTriples S D pairs := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, MultiDigraph.flatTriples, Prod.map,
      case3PushMultigraph_edgeMult_image, case3PushFlatTriples, List.flatMap_cons,
      List.cons_append, List.nil_append] at *
    rw [ih]

/-- The complete restored encoding maps only endpoint labels in the
positive-pair records, retaining the original directed multiplicities. -/
theorem case3PushMultigraph_enc {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).enc =
      [N, D.numActivePairs] ++ case3PushFlatTriples S D D.activePairsList := by
  unfold MultiDigraph.enc
  rw [case3PushMultigraph_numActivePairs, case3PushMultigraph_activePairs, case3PushFlatTriples_eq]

/-- Restoring labels changes no encoding length. -/
theorem case3PushMultigraph_enc_length {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).enc.length = D.enc.length := by
  rw [MultiDigraph.length_enc, MultiDigraph.length_enc, case3PushMultigraph_numActivePairs]

end GraphMinor.Compute
