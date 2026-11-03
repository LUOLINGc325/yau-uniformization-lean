import Yau.Proofs.V04FejerConvolution
import Yau.Proofs.V03GagliardoCircle

/-! Exact finite Fourier support controls the original half-order
seminorm by the actual L2 integral. The shift preserves the uniform norm
and is fixed before the circle point. -/

open MeasureTheory AddCircle
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourierCoeff_fourier_mul (u : AddCircle T → ℂ) (m k : ℤ) :
    fourierCoeff (fun x => fourier m x * u x) k = fourierCoeff u (k - m) := by
  unfold fourierCoeff
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  have heq : -k + m = -(k - m) := by omega
  rw [heq]

theorem circleDirichlet_bandwidth_le {u : AddCircle T → ℂ} (hu : Continuous u)
    {N : ℝ} (hN : 0 ≤ N) (hsupp : ∀ k : ℤ, N < |(k : ℝ)| → fourierCoeff u k = 0) :
    circleDirichlet u ≤ ENNReal.ofReal N *
      ENNReal.ofReal (∫ x : AddCircle T, ‖u x‖ ^ 2 ∂haarAddCircle) := by
  have hp := circle_parseval_continuous hu
  rw [← hp.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.summable,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [← ENNReal.ofReal_mul hN]
  by_cases hk : |(k : ℝ)| ≤ N
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  · rw [hsupp k (lt_of_not_ge hk)]
    simp

theorem shifted_scalarFejer_support (u : AddCircle T → ℂ) (P : ℕ) (k : ℤ)
    (hk : (2 * P + 1 : ℝ) < |(k : ℝ)|) :
    fourierCoeff (fun x => fourier ((P + 1 : ℕ) : ℤ) x * scalarFejer u P x) k = 0 := by
  rw [fourierCoeff_fourier_mul, scalarFejer_fourierCoeff]
  have hnot : k - ((P + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(P : ℤ)) P := by
    intro hm
    have hm' := Finset.mem_Icc.mp hm
    have hk0 : 0 ≤ k := by omega
    have hkbound : k ≤ (2 * P + 1 : ℕ) := by omega
    have hkreal : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
    have hkrealbound : (k : ℝ) ≤ 2 * P + 1 := by exact_mod_cast hkbound
    rw [abs_of_nonneg hkreal] at hk
    exact (not_le_of_gt hk) hkrealbound
  rw [fejerMultiplier, if_neg hnot]
  simp

theorem shifted_scalarFejer_dirichlet_le {u : AddCircle T → ℂ} (hu : Continuous u)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖u x‖ ≤ M) (P : ℕ) :
    circleDirichlet (fun x => fourier ((P + 1 : ℕ) : ℤ) x * scalarFejer u P x) ≤
      ENNReal.ofReal ((2 * P + 1 : ℝ) * M ^ 2) := by
  let v := fun x : AddCircle T => fourier ((P + 1 : ℕ) : ℤ) x * scalarFejer u P x
  have hv : Continuous v := (fourier _).continuous.mul (scalarFejer_continuous u P)
  have hvbound (x : AddCircle T) : ‖v x‖ ^ 2 ≤ M ^ 2 := by
    dsimp only [v]
    rw [norm_mul, fourier_point_norm, one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (scalarFejer_norm_le hu hbound P x)
  have hint : (∫ x : AddCircle T, ‖v x‖ ^ 2 ∂haarAddCircle) ≤ M ^ 2 := by
    have hh := integral_mono
      ((hv.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const (μ := (haarAddCircle : Measure (AddCircle T))) (M ^ 2)) hvbound
    simpa using hh
  have hh := circleDirichlet_bandwidth_le hv (by positivity : (0 : ℝ) ≤ 2 * P + 1)
    (shifted_scalarFejer_support u P)
  exact (hh.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hint) bot_le)).trans_eq
    (ENNReal.ofReal_mul (by positivity)).symm

end Yau.Blueprint.V04Proof
