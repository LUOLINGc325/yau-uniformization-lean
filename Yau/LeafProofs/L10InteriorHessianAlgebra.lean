import Yau.LeafProofs.L10InteriorEnergyAlgebra

/-! Numerical absorption for the differentiated divergence energy identity. -/

noncomputable section

namespace Yau.LeafProofs

def ellipticHessianMixedConstant (N _ell A B M : ℝ) : ℝ :=
  N^3 * A * (1 + 2 * M) + N^2 * B + N

def ellipticHessianAbsorptionConstant (N ell A B M : ℝ) : ℝ :=
  (ellipticHessianMixedConstant N ell A B M)^2 / ell +
    2 * N^3 * M * A + N * M + 2 * N^2 * M * B + 1

theorem ellipticHessianAbsorptionConstant_pos {N ell A B M : ℝ}
    (hN : 0 ≤ N) (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    0 < ellipticHessianAbsorptionConstant N ell A B M := by
  unfold ellipticHessianAbsorptionConstant
  positivity

theorem elliptic_hessian_scalar_absorption {N ell A B M X G F : ℝ}
    (hN : 0 ≤ N) (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hX : 0 ≤ X) (hG : 0 ≤ G) (hF : 0 ≤ F) :
    (N^3 * A + 2 * N^3 * M * A) * X * G + 2 * N^3 * M * A * G^2 +
      N * X * (F + N * B * G) + 2 * N * M * G * (F + N * B * G) ≤
        ell / 2 * X^2 + ellipticHessianAbsorptionConstant N ell A B M * (G^2 + F^2) := by
  let K := ellipticHessianMixedConstant N ell A B M
  let L := N^3 * A + 2 * N^3 * M * A + N^2 * B
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hK : 0 ≤ K := by dsimp only [K, ellipticHessianMixedConstant]; positivity
  have hKN : K = L + N := by dsimp only [K, L, ellipticHessianMixedConstant]; ring
  have hMixed : L * X * G + N * X * F ≤ K * X * (G + F) := by
    rw [hKN]
    nlinarith [mul_nonneg (mul_nonneg hN hX) hG, mul_nonneg (mul_nonneg hL hX) hF]
  have hY := elliptic_young (x := X) (y := K * (G + F)) hell
  rw [abs_of_nonneg (by positivity : 0 ≤ X * (K * (G + F)))] at hY
  have hSquare : (K * (G + F))^2 ≤ 2 * K^2 * (G^2 + F^2) := by
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg (G - F))]
  have hDivide : (K * (G + F))^2 / (2 * ell) ≤ K^2 / ell * (G^2 + F^2) := by
    calc
      _ ≤ (2 * K^2 * (G^2 + F^2)) / (2 * ell) :=
        div_le_div_of_nonneg_right hSquare (by positivity)
      _ = _ := by ring
  have hSource : 2 * N * M * G * F ≤ N * M * (G^2 + F^2) := by
    nlinarith [mul_nonneg (mul_nonneg hN hM) (sq_nonneg (G - F))]
  have hExtraG : 0 ≤ (2 * N^3 * M * A + 2 * N^2 * M * B) * F^2 := by positivity
  have hExtra : 0 ≤ G^2 + F^2 := by positivity
  dsimp only [ellipticHessianAbsorptionConstant]
  change _ ≤ ell / 2 * X^2 +
    (K^2 / ell + 2 * N^3 * M * A + N * M + 2 * N^2 * M * B + 1) * (G^2 + F^2)
  dsimp only [L] at hMixed
  nlinarith

end Yau.LeafProofs
