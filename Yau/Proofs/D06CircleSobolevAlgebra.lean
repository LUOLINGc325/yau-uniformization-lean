import Yau.Proofs.D06CircleWeakLeibniz
import Yau.Proofs.D06CircleSobolevDerivative

/-! The one-dimensional Fourier Sobolev algebra property, with weak Leibniz
and the actual original circle products at every induction step. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleCoeff_add (f g : CircleL2) (n : ℤ) :
    circleCoeff (f + g) n = circleCoeff f n + circleCoeff g n := by
  change ((fourierBasis (T := 2 * Real.pi)).repr (f + g)) n = _
  rw [map_add]
  rfl

theorem circleSobolev_add {k : ℕ} {f g : CircleL2}
    (hf : CircleSobolev k f) (hg : CircleSobolev k g) : CircleSobolev k (f + g) := by
  apply ((hf.add hg).mul_left 2).of_nonneg_of_le
    (fun _ => mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
  intro n
  rw [circleCoeff_add]
  have hn : ‖circleCoeff f n + circleCoeff g n‖ ^ 2 ≤
      2 * ‖circleCoeff f n‖ ^ 2 + 2 * ‖circleCoeff g n‖ ^ 2 := by
    have h := norm_add_le (circleCoeff f n) (circleCoeff g n)
    nlinarith [norm_nonneg (circleCoeff f n + circleCoeff g n), norm_nonneg (circleCoeff f n),
      norm_nonneg (circleCoeff g n), sq_nonneg (‖circleCoeff f n‖ - ‖circleCoeff g n‖)]
  have h := mul_le_mul_of_nonneg_left hn (pow_nonneg (by positivity : 0 ≤ 1 + (n : ℝ) ^ 2) k)
  nlinarith only [h]

theorem circleProduct_sobolev_succ (k : ℕ) {f g : CircleL2}
    (hf : CircleSobolev (k + 1) f) (hg : CircleSobolev (k + 1) g) :
    CircleSobolev (k + 1) (circleProduct f g) := by
  induction k generalizing f g with
  | zero =>
    let df := circleDerivative f hf
    let dg := circleDerivative g hg
    have hD := circleWeakDerivative_product hf hg (circleDerivative_weak f hf) (circleDerivative_weak g hg)
    exact circleSobolev_succ_of_derivative 0 hD (circleSobolev_zero _) (circleSobolev_zero _)
  | succ k ih =>
    have hf1 : CircleSobolev 1 f := circleSobolev_mono hf (by omega)
    have hg1 : CircleSobolev 1 g := circleSobolev_mono hg (by omega)
    let df := circleDerivative f hf1
    let dg := circleDerivative g hg1
    have hdf : CircleSobolev (k + 1) df := circleDerivative_sobolev (k + 1) hf
    have hdg : CircleSobolev (k + 1) dg := circleDerivative_sobolev (k + 1) hg
    have hfk : CircleSobolev (k + 1) f := circleSobolev_mono hf (by omega)
    have hgk : CircleSobolev (k + 1) g := circleSobolev_mono hg (by omega)
    have hsum := circleSobolev_add (ih hdf hgk) (ih hdg hfk)
    have hD := circleWeakDerivative_product hf1 hg1 (circleDerivative_weak f hf1) (circleDerivative_weak g hg1)
    exact circleSobolev_succ_of_derivative (k + 1) hD (ih hfk hgk) hsum

end Yau.NodeProofs.D06Aux
