import Yau.Proofs.V04ClockLiftCandidate
import Yau.Proofs.V03ConjugateTrace
import Yau.Proofs.V03BoundaryHilbertDifference

/-! The actual holomorphic clock lift has twice the real weight's
homogeneous Fourier energy. The zero Fourier mode never contributes. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem scalarDSq_sub_constant {γ : ℝ → ℝ} (hγ : Continuous γ)
    (hp : Function.Periodic γ (2 * Real.pi)) (c : ℝ) :
    scalarDSq (fun θ => γ θ - c) = scalarDSq γ := by
  have hc : Continuous (fun θ => ((γ θ - c : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hγ.sub continuous_const)
  have hg : Continuous (fun θ => (γ θ : ℂ)) := Complex.continuous_ofReal.comp hγ
  have hcp : Function.Periodic (fun θ => ((γ θ - c : ℝ) : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg (fun x : ℝ => ((x - c : ℝ) : ℂ)) (hp θ)
  have hgp : Function.Periodic (fun θ => (γ θ : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg Complex.ofReal (hp θ)
  have heq (θ τ : ℝ) : ((γ θ - c : ℝ) : ℂ) - ((γ τ - c : ℝ) : ℂ) =
      (γ θ : ℂ) - (γ τ : ℂ) := by push_cast; ring
  have h1 := boundaryDSq_le_of_difference_bound hg hc hgp hcp (C := 1) (by norm_num)
    (fun θ τ => by rw [heq, one_mul])
  have h2 := boundaryDSq_le_of_difference_bound hc hg hcp hgp (C := 1) (by norm_num)
    (fun θ τ => by rw [heq, one_mul])
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at h1 h2
  exact le_antisymm h1 h2

theorem clockLiftCandidate_boundaryDSq_le {γ : ℝ → ℝ} (hγ : ContDiff ℝ ∞ γ)
    (hp : Function.Periodic γ (2 * Real.pi)) (hm : circleAverage γ = 1) :
    boundaryDSq (fun θ (_ : Unit) => clockLiftCandidate γ (circlePoint θ)) ≤
      2 * scalarDSq γ := by
  let q := fun θ => γ θ - 1
  let H := harmonicConjugateTrace q
  have hq : ContDiff ℝ ∞ q := hγ.sub contDiff_const
  have hqp : Function.Periodic q (2 * Real.pi) := fun θ => congrArg (fun x : ℝ => x - 1) (hp θ)
  have hH : ContDiff ℝ ∞ H := harmonicConjugateTrace_contDiff hq hqp
  have hHp : Function.Periodic H (2 * Real.pi) := harmonicConjugateTrace_periodic q
  have hr := (clockLiftCandidate_zero_real_boundary hγ hp hm).2
  have hi (θ : ℝ) : (clockLiftCandidate γ (circlePoint θ)).im = H θ := by
    simp only [H, harmonicConjugateTrace, clockLiftCandidate, Complex.sub_im,
      Complex.ofReal_im, sub_zero]
    rfl
  let u : ℝ → Unit ⊕ Unit → ℂ := fun θ => Sum.elim
    (fun _ => (q θ : ℂ)) (fun _ => (H θ : ℂ))
  have hu (i : Unit ⊕ Unit) : Continuous (fun θ => u θ i) := by
    cases i <;> exact Complex.continuous_ofReal.comp (by first | exact hq.continuous | exact hH.continuous)
  have hup (i : Unit ⊕ Unit) : Function.Periodic (fun θ => u θ i) (2 * Real.pi) := by
    intro θ
    cases i with
    | inl i => exact congrArg Complex.ofReal (hqp θ)
    | inr i => exact congrArg Complex.ofReal (hHp θ)
  have hv := (closedDisc_scalar_trace_contDiff (clockLiftCandidate_smooth hγ hp)).continuous
  have hvp : Function.Periodic (fun θ => clockLiftCandidate γ (circlePoint θ)) (2 * Real.pi) :=
    fun θ => congrArg (clockLiftCandidate γ) (circlePoint_periodic θ)
  have hh := boundaryDSq_le_of_sum_square_bound hu hv hup hvp (C := 1) (by norm_num)
    (fun θ τ => by
      simp only [u, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton,
        Sum.elim_inl, Sum.elim_inr, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hr, hi]
      dsimp only [q]
      nlinarith)
  simp only [ENNReal.ofReal_one, one_mul] at hh
  change _ ≤ 2 * scalarDSq γ
  calc
    _ ≤ boundaryDSq u := hh
    _ = scalarDSq q + scalarDSq H := by
      exact boundaryDSq_sum_index (fun θ (_ : Unit) => (q θ : ℂ))
        (fun θ (_ : Unit) => (H θ : ℂ))
    _ = 2 * scalarDSq γ := by
      rw [scalarDSq_harmonicConjugateTrace hq hqp, scalarDSq_sub_constant hγ.continuous hp 1]
      ring

end Yau.Blueprint.V04Proof
