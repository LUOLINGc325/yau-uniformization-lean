import Yau.Proofs.C05UnitaryHessian
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The finite Harnack cancellation and only an upper limit bound force uniform Hessian negativity. -/
noncomputable section
open Filter
open scoped Topology Matrix ComplexOrder
namespace Yau.Proofs.C05FiniteHarnackSequenceAux
open Yau.Proofs.C05Aux
variable {n : ℕ}

theorem posSemidef_trace_nonneg (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef) :
    0 ≤ M.trace.re := by
  simp only [Matrix.trace,Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => (Complex.nonneg_iff.mp (hM.diag_nonneg (i := j))).1

theorem pure_square_le_upper_error (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (M P : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef) (κ K L E : ℝ)
    (hκ : κ ≤ K)
    (hidentity : L = weightedHessianSquare lam P + (∑ j,lam j*(M j j).re) -
      2*κ*M.trace.re+weightedHessianSquare lam M-E) :
    weightedHessianSquare lam P ≤ L+2*K*M.trace.re+|E| := by
  have H := pure_square_le_harnack_error lam (fun j => (hlam j).le) M hM κ L
    (weightedHessianSquare lam P) E hidentity
  have htr := posSemidef_trace_nonneg M hM
  have hK := mul_le_mul_of_nonneg_right hκ htr
  linarith

theorem weightedPure_tendsto_zero (lam : ℕ → Fin n → ℝ)
    (hlam : ∀ i j, 0 < lam i j) (κ : ℕ → ℝ) (K : ℝ) (hκ : ∀ i, κ i ≤ K)
    (M P : ℕ → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i, (M i).PosSemidef)
    (L E : ℕ → ℝ)
    (he : Tendsto (fun i => (M i).trace.re) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0))
    (hL : ∀ ε > 0, ∀ᶠ i in atTop, L i ≤ ε)
    (hidentity : ∀ i, L i = weightedHessianSquare (lam i) (P i) +
      (∑ j,lam i j*(M i j j).re) -2*κ i*(M i).trace.re+
      weightedHessianSquare (lam i) (M i)-E i) :
    Tendsto (fun i => weightedHessianSquare (lam i) (P i)) atTop (𝓝 0) := by
  have hrest : Tendsto (fun i => 2*K*(M i).trace.re+|E i|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul he).add hE.abs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hLsmall := hL (ε/2) (half_pos hε)
  have hrestsmall := hrest.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))
  filter_upwards [hLsmall,hrestsmall] with i hiL hiR
  have H := pure_square_le_upper_error (lam i) (hlam i) (M i) (P i) (hM i)
    (κ i) K (L i) (E i) (hκ i) (hidentity i)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg
    (weightedHessianSquare_nonneg (lam i) (fun j => (hlam i j).le) (P i))]
  linarith

theorem eventually_unitaryHessian_negative (μ K : ℝ) (hμ : 0 < μ) (_hK : 0 ≤ K)
    (lam : ℕ → Fin n → ℝ) (hlam : ∀ i j, 0 < lam i j)
    (hlo : ∀ i j, μ ≤ lam i j) (hup : ∀ i j, lam i j ≤ 1)
    (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ K)
    (M P : ℕ → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i, (M i).PosSemidef)
    (L E : ℕ → ℝ)
    (he : Tendsto (fun i => (M i).trace.re) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0))
    (hL : ∀ ε > 0, ∀ᶠ i in atTop, L i ≤ ε)
    (hidentity : ∀ i, L i = weightedHessianSquare (lam i) (P i) +
      (∑ j,lam i j*(M i j j).re) -2*κ i*(M i).trace.re+
      weightedHessianSquare (lam i) (M i)-E i) :
    ∀ᶠ i in atTop, ∀ v : Fin n → ℂ,
      unitaryHessianQuadratic (M i-Matrix.diagonal
        (fun j => ((lam i j*(lam i j+κ i):ℝ):ℂ))) (P i) v ≤
          -(μ^2/2)*(2*∑ j,‖v j‖^2) := by
  have hp := weightedPure_tendsto_zero lam hlam κ K (fun i => (hκ i).2) M P hM
    L E he hE hL hidentity
  have hsmall : Tendsto (fun i => (M i).trace.re+
      (n:ℝ)*Real.sqrt (1*weightedHessianSquare (lam i) (P i))) atTop (𝓝 0) := by
    simpa using he.add (tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.comp hp))
  have hsmallEvent := hsmall.eventually
    (gt_mem_nhds (show (0:ℝ)<μ^2/2 by positivity))
  filter_upwards [hsmallEvent] with i hi
  intro v
  exact unitaryHessianQuadratic_negative (lam i) (hlam i) hμ.le (hlo i) (hup i)
    (hκ i).1 (M i) (hM i) (P i) hi.le v

theorem finite_harnack_sequence (μ K : ℝ) (hμ : 0 < μ) (hK : 0 ≤ K)
    (lam : ℕ → Fin n → ℝ) (hlam : ∀ i j, 0 < lam i j)
    (hlo : ∀ i j, μ ≤ lam i j) (hup : ∀ i j, lam i j ≤ 1)
    (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ K)
    (M P : ℕ → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i, (M i).PosSemidef)
    (L E : ℕ → ℝ)
    (he : Tendsto (fun i => (M i).trace.re) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0))
    (hL : ∀ ε > 0, ∀ᶠ i in atTop, L i ≤ ε)
    (hidentity : ∀ i, L i = weightedHessianSquare (lam i) (P i) +
      (∑ j,lam i j*(M i j j).re) -2*κ i*(M i).trace.re+
      weightedHessianSquare (lam i) (M i)-E i) :
    Tendsto (fun i => weightedHessianSquare (lam i) (P i)) atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, ∀ v : Fin n → ℂ,
        unitaryHessianQuadratic (M i-Matrix.diagonal
          (fun j => ((lam i j*(lam i j+κ i):ℝ):ℂ))) (P i) v ≤
            -(μ^2/2)*(2*∑ j,‖v j‖^2) := by
  exact ⟨weightedPure_tendsto_zero lam hlam κ K (fun i => (hκ i).2) M P hM L E he hE hL hidentity,
    eventually_unitaryHessian_negative μ K hμ hK lam hlam hlo hup κ hκ M P hM L E he hE hL hidentity⟩

end Yau.Proofs.C05FiniteHarnackSequenceAux
