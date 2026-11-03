import Mathlib.Topology.Path

/-! A genuine based square ending at any continuous loop, with no regularity assumption on that loop. -/
noncomputable section
open scoped Topology unitInterval
namespace Yau.Proofs.C05LoopIngressAux

def loopPrefixParameter (p : I × I) : I :=
  ⟨(p.1 : ℝ) * (1 + (p.2 : ℝ)) / 2, by
    constructor
    · exact div_nonneg (mul_nonneg p.1.2.1 (by linarith [p.2.2.1])) (by norm_num)
    · have H := mul_le_mul_of_nonneg_right p.1.2.2
        (show 0 ≤ 1 + (p.2 : ℝ) by linarith [p.2.2.1])
      nlinarith only [H, p.2.2.2]⟩

theorem loopPrefixParameter_continuous : Continuous loopPrefixParameter := by
  apply Continuous.subtype_mk
  fun_prop

theorem exists_based_square_ending_loop {P : Type*} [TopologicalSpace P]
    {o x : P} (δ : Path o x) (γ : Path x x) :
    ∃ H : C(I × I, P), (∀ s : I, H (0, s) = o) ∧ ∀ s : I, H (1, s) = γ s := by
  let joined := δ.trans γ
  let H : C(I × I, P) := ⟨fun p => joined (loopPrefixParameter p),
    joined.continuous.comp loopPrefixParameter_continuous⟩
  refine ⟨H, ?_, ?_⟩
  · intro s
    have hzero : loopPrefixParameter (0, s) = 0 := by
      apply Subtype.ext
      change (0 : ℝ) * (1 + (s : ℝ)) / 2 = 0
      ring
    change joined (loopPrefixParameter (0, s)) = o
    rw [hzero]
    exact joined.source
  · intro s
    change joined (loopPrefixParameter (1, s)) = γ s
    have hval : ((loopPrefixParameter (1, s) : I) : ℝ) = (1 + (s : ℝ)) / 2 := by
      change (1 : ℝ) * (1 + (s : ℝ)) / 2 = _
      ring
    calc
      _ = joined.extend ((1 + (s : ℝ)) / 2) := by
        rw [← hval]
        exact (Path.extend_apply joined (loopPrefixParameter (1, s)).2).symm
      _ = γ.extend (2 * ((1 + (s : ℝ)) / 2) - 1) :=
        Path.extend_trans_of_half_le δ γ (by linarith [s.2.1])
      _ = γ.extend (s : ℝ) := by congr 1; ring
      _ = γ s := Path.extend_apply γ s.2

end Yau.Proofs.C05LoopIngressAux
