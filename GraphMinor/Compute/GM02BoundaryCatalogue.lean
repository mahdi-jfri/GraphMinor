module

public import GraphMinor.Compute.GM02BoundarySchemeSet
public import GraphMinor.Compute.GM02BoundaryEncoding
public import GraphMinor.Compute.GM02FiniteTrie

/-!
# The finite boundary-catalogue Word RAM program

For a fixed boundary bound, a fixed finite prefix tree reads the plain
boundary input. Its leaves store the binary catalogue of all valid
crossing-scheme data codes for that input. The input has only original
terminal pairs and side flags. The tree computes the catalogue in time
bounded solely by the fixed boundary bound and leaves every array intact.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Complete boundary encodings in the fixed finite input range. -/
def gm02BoundaryComplete (N : ℕ) (words : List ℕ) : Prop :=
  ∃ x : GM02BoundaryInput, x.n ≤ N ∧ x.enc = words

/-- The fixed finite table of catalogues, indexed only by plain input words. -/
noncomputable def gm02BoundaryCatalogueAnswer (N : ℕ) (words : List ℕ) : ℕ :=
  if h : ∃ x : GM02BoundaryInput, x.n ≤ N ∧ x.enc = words then
    gm02BoundarySchemeSetCode N h.choose else 0

/-- The catalogue table is uniformly bounded, including unused prefixes. -/
theorem gm02BoundaryCatalogueAnswer_lt (N : ℕ) (words : List ℕ) :
    gm02BoundaryCatalogueAnswer N words < 2 ^ gm02BoundarySchemeCodeBound N := by
  unfold gm02BoundaryCatalogueAnswer
  split_ifs
  · exact gm02BoundarySchemeSetCode_lt N _
  · exact Nat.two_pow_pos _

/-- Encoding injectivity identifies the table entry with the actual instance. -/
theorem gm02BoundaryCatalogueAnswer_enc (N : ℕ) (x : GM02BoundaryInput) (hn : x.n ≤ N) :
    gm02BoundaryCatalogueAnswer N x.enc = gm02BoundarySchemeSetCode N x := by
  have hex : ∃ y : GM02BoundaryInput, y.n ≤ N ∧ y.enc = x.enc := ⟨x, hn, rfl⟩
  rw [gm02BoundaryCatalogueAnswer, dite_eq_left hex]
  have hy : hex.choose = x := gm02BoundaryEncoding_injective hex.choose_spec.2
  rw [hy]

/-- On a valid boundary input, completion is detected exactly at its end. -/
theorem gm02BoundaryComplete_take (N : ℕ) (x : GM02BoundaryInput) (hn : x.n ≤ N)
    (m : ℕ) (hm : m ≤ x.enc.length) :
    gm02BoundaryComplete N (x.enc.take m) ↔ m = x.enc.length := by
  constructor
  · rintro ⟨y, _, hy⟩
    have hp : y.enc ++ x.enc.drop m = x.enc := by rw [hy, List.take_append_drop]
    have hd := gm02BoundaryEncoding_prefix_free y x (x.enc.drop m) hp
    have hl := congrArg List.length hp
    rw [hd, List.length_append, List.length_nil, Nat.add_zero, hy, List.length_take_of_le hm] at hl
    exact hl
  · intro he
    subst m
    exact ⟨x, hn, List.take_length.symm⟩

/-- A fixed prefix-tree program producing the boundary-scheme catalogue. -/
noncomputable def gm02BoundaryCatalogueProg (N : ℕ) (src : Arr) (r_out r_tmp : Reg) : Cmd :=
  gm02FiniteTrieProg src r_out r_tmp (N * N + N + 1) (gm02BoundaryComplete N)
    (gm02BoundaryCatalogueAnswer N) (3 + 3 * N) []

/-- The catalogue program runs on plain boundary encodings, returns exactly
all valid scheme codes, and preserves every array. Its time is constant
for the fixed boundary bound. -/
theorem gm02BoundaryCatalogueProg_exec {w N : ℕ} (src : Arr) (r_out r_tmp : Reg)
    (x : GM02BoundaryInput) (hn : x.n ≤ N) (rest : List ℕ) (s : State)
    (hsrc : s.arrs src = x.enc ++ rest)
    (hwords : N * N + N + 2 < 2 ^ w) (hdepth : 3 + 3 * N < 2 ^ w)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) :
    ∃ s' t, Exec w (gm02BoundaryCatalogueProg N src r_out r_tmp) s s' t ∧
      t ≤ (4 + 3 * N) * (4 * (N * N + N + 1) + 10) ∧
      s'.regs r_out = gm02BoundarySchemeSetCode N x ∧
      (∀ r, r ≠ r_out → r ≠ r_tmp → s'.regs r = s.regs r) ∧ s'.arrs = s.arrs := by
  have hl := x.enc_length_le hn
  obtain ⟨s', t, he, ht, hout, hr, ha⟩ := gm02FiniteTrieProg_exec src r_out r_tmp
    (N * N + N + 1) (gm02BoundaryComplete N) (gm02BoundaryCatalogueAnswer N)
    (fun pref => (gm02BoundaryCatalogueAnswer_lt N pref).trans_le hcodes) x.enc rest
    (gm02BoundaryComplete_take N x hn) (fun v hv => x.enc_word_le hn hv)
    (by omega) (by omega) (3 + 3 * N) 0 (Nat.zero_le _) (by omega) hdepth s hsrc
  refine ⟨s', t, he, ?_, hout.trans (gm02BoundaryCatalogueAnswer_enc N x hn), hr, ha⟩
  have heq : 3 + 3 * N + 1 = 4 + 3 * N := by omega
  simpa only [heq] using ht

end GraphMinor.Compute
