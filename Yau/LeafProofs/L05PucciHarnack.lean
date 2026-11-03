import Yau.LeafProofs.L05PucciHarnackGridDecay
import Yau.LeafProofs.L05PucciHarnackMoment

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem pucci_weak_harnack {n : ℕ} (hn : 0 < n) {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧ ∀ v : Point n → ℝ,
      ContinuousOn v (unitClosed n) → (∀ z∈unitClosed n, 0 ≤ v z) →
      viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => -1) v →
      ∀ z∈harnackQplus n,
        ((∫ y in harnackQminus n, (v y)^p)/((volume : Measure (Point n)) (harnackQminus n)).toReal)^(1/p)
          ≤ C*(v z+1) := by
  obtain ⟨H0,K,q,A,hH0,hK,hq0,hq1,hA,hDistribution⟩ := harnack_distribution_decay hn hell hL
  let p := harnackMomentExponent q K
  have hp := harnack_momentExponent_bounds hq0 hq1 hK
  let C := harnackMomentNormConstant H0 K q A p (harnackMu (harnackQminus n))
  have hC : 0 < C := harnack_momentNormConstant_pos hH0 hK hA.le (harnack_qminus_mu_pos n) hp.2.2
  refine ⟨p,C,hp.1,hp.2.1,hC,?_⟩
  intro v hv hv0 hSuper z hz
  let h := v z+1
  have hh : 0 < h := by have hz0 := hv0 z (harnack_qplus_subset_unitClosed hz); dsimp only [h]; linarith
  let u : Point n → ℝ := fun y => (v y+y.2+1)/h
  have hu : harnackSuper0 ell L u := harnack_super0_div hell.le hL hh (harnack_homogenize hv hv0 hSuper)
  have huz : u z ≤ 1 := by
    apply (div_le_iff₀ hh).mpr
    dsimp only [h]
    linarith [hz.2.2]
  have hMoment := harnack_geometric_moment_norm hu.1 hu.2.1 (harnack_qminus_isOpen n).measurableSet
    harnack_qminus_subset_unitClosed (harnack_qminus_mu_pos n) hH0 hK hq0.le hA.le hp.1 hp.2.2
    (hDistribution u hu ⟨z,hz,huz⟩)
  have hScale := harnack_moment_norm_scale hu.1 hv hu.2.1 hv0 (harnack_qminus_isOpen n).measurableSet
    harnack_qminus_subset_unitClosed (harnack_qminus_mu_pos n) hh hp.1 (fun y hy => by
      dsimp only [u]
      rw [mul_div_cancel₀ _ hh.ne']
      have ht := (harnack_qminus_subset_unitClosed hy).2.1
      linarith)
  change _ ≤ C*h
  exact hScale.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hMoment hh.le)

end Yau.LeafProofs.L05Aux
