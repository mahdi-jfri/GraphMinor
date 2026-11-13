module

public import GraphMinor.Compute.Menger
import Mathlib.Tactic

/-!
# Reading a returned path from successor words

After the successful maximum-flow phase of VI (5.11), page 134,
the used, predecessor and successor words describe a full path system.
Follow the successor words for at most the vertex count steps. This
pure finite operation reads no proof or chosen geometric path. Its
vertex list agrees exactly with the path extracted by the verified
Menger library, and hence has no repeated vertex when started at a
path source.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Follow the raw successor words with a finite step budget. The
sentinel value `n` ends the path. -/
def gm06Alg511SuccVertices (n : ℕ) (out : List ℕ) : ℕ → ℕ → List ℕ
  | 0, start => [start]
  | fuel + 1, start =>
      if out.getD (1 + 2 * n + start) n < n then
        start :: gm06Alg511SuccVertices n out fuel (out.getD (1 + 2 * n + start) n)
      else [start]

/-- Reading the successor words gives exactly the vertex sequence
of the library's finite trace walk, without choosing a path. -/
theorem gm06Alg511SuccVertices_eq_traceWalk {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (out : List ℕ)
    (hsys : IsValidPathSystem G A B (decUsed n out) (decPred n out) (decSucc n out))
    (fuel : ℕ) (u : Fin n) :
    gm06Alg511SuccVertices n out fuel u.val =
      (traceWalk hsys fuel u).2.support.map Fin.val := by
  induction fuel generalizing u with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : decSucc n out u < n
    · rw [traceWalk_succ_of_lt hsys fuel u h]
      change (if out.getD (1 + 2 * n + u.val) n < n then
          u.val :: gm06Alg511SuccVertices n out fuel (out.getD (1 + 2 * n + u.val) n)
          else [u.val]) = u.val :: _
      have hraw : out.getD (1 + 2 * n + u.val) n < n := h
      rw [ite_eq_left hraw]
      congr 1
      exact ih ⟨decSucc n out u, h⟩
    · rw [traceWalk_succ_of_not_lt hsys fuel u h]
      change (if out.getD (1 + 2 * n + u.val) n < n then
          u.val :: gm06Alg511SuccVertices n out fuel (out.getD (1 + 2 * n + u.val) n)
          else [u.val]) = [u.val]
      have hraw : ¬ out.getD (1 + 2 * n + u.val) n < n := h
      rw [ite_eq_right hraw]

/-- A source of the returned valid path system has a repetition-free
raw successor trace, with at most `n` vertices. -/
theorem gm06Alg511SuccVertices_nodup_length {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (out : List ℕ)
    (hsys : IsValidPathSystem G A B (decUsed n out) (decPred n out) (decSucc n out))
    (u : Fin n) (hu : u ∈ pathStarts (decUsed n out) (decPred n out)) :
    (gm06Alg511SuccVertices n out n u.val).Nodup ∧
      (gm06Alg511SuccVertices n out n u.val).length ≤ n := by
  rw [gm06Alg511SuccVertices_eq_traceWalk out hsys]
  have hp := abWalkOfStart_isPath hsys u hu
  have hnd : (traceWalk hsys n u).2.support.Nodup := hp.support_nodup
  refine ⟨hnd.map Fin.val_injective, ?_⟩
  rw [List.length_map]
  simpa only [Fintype.card_fin] using hnd.length_le_card

end GraphMinor.Compute
