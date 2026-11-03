import Yau.LeafProofs.L05PerturbationForcing
import Mathlib.Analysis.MeanInequalitiesPow

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_two_early_means {n : ℕ} {p D : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hD : 0 ≤ D) {v w : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (hw : ContinuousOn w (unitClosed n))
    (hv0 : ∀ z∈unitClosed n, 0 ≤ v z) (hw0 : ∀ z∈unitClosed n, 0 ≤ w z)
    (hSum : ∀ z∈harnackQminus n, v z+w z=D) :
    (1/2 : ℝ)^(1/p)*D ≤ perturbEarlyMean p v ∨
      (1/2 : ℝ)^(1/p)*D ≤ perturbEarlyMean p w := by
  let E := harnackQminus n
  let V := harnackMu E
  have hV : 0 < V := harnack_qminus_mu_pos n
  have hCompact : IsCompact (unitClosed n) :=
    (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hVi : IntegrableOn (fun z => (v z)^p) E :=
    ((hv.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hCompact).mono_set
      harnack_qminus_subset_unitClosed
  have hWi : IntegrableOn (fun z => (w z)^p) E :=
    ((hw.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hCompact).mono_set
      harnack_qminus_subset_unitClosed
  have hDi : IntegrableOn (fun _ : Point n => D^p) E :=
    (continuousOn_const.integrableOn_compact hCompact).mono_set harnack_qminus_subset_unitClosed
  have hIntegral : (∫ z in E, D^p) ≤ ∫ z in E, (v z)^p+(w z)^p := by
    apply integral_mono_ae hDi (hVi.add hWi)
    filter_upwards [ae_restrict_mem (harnack_qminus_isOpen n).measurableSet] with z hz
    rw [← hSum z hz]
    exact Real.rpow_add_le_add_rpow (hv0 z (harnack_qminus_subset_unitClosed hz))
      (hw0 z (harnack_qminus_subset_unitClosed hz)) hp.le hp1
  have hAvg : D^p ≤ (∫ z in E, (v z)^p)/V+(∫ z in E, (w z)^p)/V := by
    calc
      D^p = (∫ _ : Point n in E, D^p)/V := by
        rw [setIntegral_const]
        change D^p=V*D^p/V
        field_simp [hV.ne']
      _ ≤ (∫ z in E, (v z)^p+(w z)^p)/V :=
        div_le_div_of_nonneg_right hIntegral hV.le
      _ = _ := by rw [integral_add hVi hWi]; ring
  have hChoice : D^p/2 ≤ (∫ z in E, (v z)^p)/V ∨
      D^p/2 ≤ (∫ z in E, (w z)^p)/V := by
    by_contra h
    push_neg at h
    linarith
  have hRoot : (D^p/2)^(1/p)=(1/2 : ℝ)^(1/p)*D := by
    rw [show D^p/2=(1/2 : ℝ)*(D^p) from by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) (Real.rpow_nonneg hD p),
      ← Real.rpow_mul hD,show p*(1/p)=1 from by field_simp [hp.ne'],Real.rpow_one]
  rcases hChoice with h | h
  · left
    have hh := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hD p) (by norm_num)) h
      (one_div_pos.mpr hp).le
    rwa [hRoot] at hh
  · right
    have hh := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hD p) (by norm_num)) h
      (one_div_pos.mpr hp).le
    rwa [hRoot] at hh

end Yau.LeafProofs.L05Aux
