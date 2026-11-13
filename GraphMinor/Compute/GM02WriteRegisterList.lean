module

public import GraphMinor.Compute.Basic
import GraphMinor.Compute.Algorithm44ModelBridge
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Writing a fixed list of chosen endpoint registers

For the fixed pattern in II (4.7), every edge end has a fixed decoded
register. Write any such fixed register list into an allocated buffer.
The proof follows the list, extending the written prefix by one word
at each step, and records exact time and preservation of all registers.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Store the indicated registers at consecutive fixed array positions. -/
@[expose] def gm02WriteRegisterListProg (dst : Arr) (off : ℕ) : List Reg → Cmd
  | [] => .skip
  | r :: rs => .seq (.write dst (.const off) (.reg r))
      (gm02WriteRegisterListProg dst (off + 1) rs)

/-- A fixed register list is written exactly, retaining every register and unrelated array. -/
theorem gm02WriteRegisterListProg_exec {W : ℕ} (dst : Arr) (rs : List Reg)
    (pre : List ℕ) (s : State)
    (hbuf : s.arrs dst = pre ++ List.replicate rs.length 0)
    (hcap : pre.length + rs.length < 2 ^ W)
    (hwords : ∀ r ∈ rs, s.regs r < 2 ^ W) :
    ∃ s', Exec W (gm02WriteRegisterListProg dst pre.length rs) s s' (1 + 3 * rs.length) ∧
      s'.arrs dst = pre ++ rs.map s.regs ∧ s'.regs = s.regs ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  induction rs generalizing pre s with
  | nil =>
    exact ⟨s, .skip s, by simpa only [List.length_nil, List.replicate_zero,
      List.map_nil, List.append_nil] using hbuf, rfl, fun _ _ => rfl⟩
  | cons r rs ih =>
    let s₁ := s.writeArr dst pre.length (s.regs r)
    have hi : pre.length < (s.arrs dst).length := by
      simp only [hbuf, List.length_append, List.length_replicate, List.length_cons]
      omega
    have he₁ : Exec W (.write dst (.const pre.length) (.reg r)) s s₁ 3 :=
      .write (eval_const (by simp only [List.length_cons] at hcap; omega))
        (eval_reg rfl (hwords r (List.mem_cons_self))) hi
    have hb₁ : s₁.arrs dst = (pre ++ [s.regs r]) ++ List.replicate rs.length 0 := by
      rw [show s₁.arrs dst = (s.arrs dst).set pre.length (s.regs r) from State.writeArr_arrs_self .., hbuf]
      exact set_append_replicate_succ pre rs.length (s.regs r)
    have hcap₁ : (pre ++ [s.regs r]).length + rs.length < 2 ^ W := by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hcap
      omega
    obtain ⟨s₂, he₂, hout, hr₂, ha₂⟩ := ih (pre ++ [s.regs r]) s₁ hb₁ hcap₁
      (fun a ha => hwords a (List.mem_cons_of_mem r ha))
    refine ⟨s₂, ?_, ?_, hr₂, ?_⟩
    · have he := Exec.seq he₁ he₂
      simpa only [gm02WriteRegisterListProg, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd,
        Nat.add_comm 3] using he
    · simpa only [s₁, State.writeArr_regs, List.map_cons, List.append_assoc,
        List.singleton_append] using hout
    · intro a ha
      exact (ha₂ a ha).trans (State.writeArr_arrs_ne s pre.length (s.regs r) ha)

end GraphMinor.Compute
