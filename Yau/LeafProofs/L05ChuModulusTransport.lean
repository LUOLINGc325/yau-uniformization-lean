import Yau.LeafProofs.L05ChuHessianTransport
import Yau.LeafProofs.L05ChuWeightedCutoff

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem chu_hessian_difference_norm_le {n : ℕ} (u : Point n → ℝ) (p q : Point n) :
    ‖hessian u p-hessian u q‖ ≤ chuHessianTransportConstant n*‖spatialDD u p-spatialDD u q‖ := by
  have hn := chuHessianBilinear_norm_le (spatialDD u p-spatialDD u q)
  have he := (chuHessianBilinearLinear n).map_sub (spatialDD u p) (spatialDD u q)
  rw [he] at hn
  exact hn

theorem chu_hessian_oscillation_le {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ} {M r : ℝ}
    (hM : 0 ≤ M) (hDD : ∀ p ∈ Q, ‖spatialDD u p‖ ≤ M) :
    chuOscillation Q (hessian u) r ≤ chuHessianTransportConstant n*chuOscillation Q (spatialDD u) r := by
  have hC := (chuHessianTransportConstant_pos n).le
  apply chuOscillation_le (mul_nonneg hC (chuOscillation_nonneg hM hDD r))
  intro p hp q hq hpq
  have ht := chuOscillation_pair_le (J := spatialDD u) hM hDD hp hq hpq
  exact (chu_hessian_difference_norm_le u p q).trans
    (mul_le_mul_of_nonneg_left ht hC)

theorem chu_oscillation_add_holder {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    {Q : Set (Point n)} {g b : Point n → V} {J : Point n → W}
    {epsilon A gamma M C r : ℝ} (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hg : 0 ≤ gamma) (hr : 0 ≤ r) (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M)
    (hb : HolderBound gamma Q b C)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, parabolicDistance p q ≤ r →
      ‖g p-g q‖ ≤ epsilon*‖J p-J q‖+A*r^gamma) :
    chuOscillation Q (fun p => g p+b p) r ≤ epsilon*chuOscillation Q J r+(A+2*C)*r^gamma := by
  have hC : 0 ≤ C := hb.1
  apply chuOscillation_perturbation heps (by positivity) hM hr hJ
  intro p hp q hq hpq
  have he : (g p+b p)-(g q+b q)=(g p-g q)+(b p-b q) := by abel
  rw [he]
  have hn := norm_add_le (g p-g q) (b p-b q)
  have hbnd := (hb.2.2 p hp q hq).trans
    (mul_le_mul_of_nonneg_left (holderWeight_le_twice_radius_power hg hpq) hb.1)
  have hh := hpair p hp q hq hpq
  nlinarith only [hn,hbnd,hh]

end Yau.LeafProofs.L05Aux
