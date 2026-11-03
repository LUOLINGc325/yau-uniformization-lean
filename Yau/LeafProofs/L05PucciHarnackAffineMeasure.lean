import Yau.LeafProofs.L05PucciHarnackDomains

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackAffineJacobian (n : ℕ) (R T : ℝ) : ℝ := R^(2*n)*T

theorem harnack_affineJacobian_pos {n : ℕ} {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    0 < harnackAffineJacobian n R T := mul_pos (pow_pos hR _) hT

theorem harnack_map_affineLinear_volume {n : ℕ} {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    Measure.map (harnackAffineLinear n R T) (volume : Measure (Point n))=
      ENNReal.ofReal ((harnackAffineJacobian n R T)⁻¹) • (volume : Measure (Point n)) := by
  have hSpace := Measure.map_addHaar_smul (volume : Measure (Space n)) hR.ne'
  rw [complexVector_finrank_real,abs_of_pos (inv_pos.mpr (pow_pos hR _))] at hSpace
  have hTime := Measure.map_addHaar_smul (volume : Measure ℝ) hT.ne'
  simp only [Module.finrank_self,pow_one,abs_of_pos (inv_pos.mpr hT)] at hTime
  have hMap : (harnackAffineLinear n R T : Point n → Point n)=
      Prod.map (fun x : Space n => R • x) (fun t : ℝ => T • t) := rfl
  rw [hMap,Measure.volume_eq_prod,← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    hSpace,hTime,Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (R^(2*n))⁻¹)]
  have hCoef : (R^(2*n))⁻¹*T⁻¹=(harnackAffineJacobian n R T)⁻¹ := by
    simp only [harnackAffineJacobian,mul_inv]
  rw [hCoef]

theorem harnack_map_affine_volume {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) :
    Measure.map (harnackAffine c R a T) (volume : Measure (Point n))=
      ENNReal.ofReal ((harnackAffineJacobian n R T)⁻¹) • (volume : Measure (Point n)) := by
  let harnackAffineMeasure_pointHaar : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  change Measure.map ((fun p : Point n => p+(c,a+T)) ∘ harnackAffineLinear n R T) volume=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),harnack_map_affineLinear_volume hR hT,
    Measure.map_smul _ (by fun_prop),Measure.IsAddRightInvariant.map_add_right_eq_self]

theorem harnack_map_affine_open_volume {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) :
    Measure.map (harnackAffine c R a T) (volume.restrict (unitOpen n))=
      ENNReal.ofReal ((harnackAffineJacobian n R T)⁻¹) •
        (volume : Measure (Point n)).restrict (harnackOpen c R a T) := by
  have hPre : harnackAffine c R a T ⁻¹' harnackOpen c R a T=unitOpen n := by
    ext z
    exact harnack_affine_open_mem_iff c hR hT z
  have h := Measure.restrict_map (μ := (volume : Measure (Point n)))
    (harnack_affine_contDiff c R a T).continuous.measurable
    (show MeasurableSet (harnackOpen c R a T) from (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet)
  rw [hPre,harnack_map_affine_volume c hR hT,Measure.restrict_smul] at h
  exact h.symm

theorem harnack_integral_affine_open {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (g : Point n → ℝ) :
    (∫ z in unitOpen n, g (harnackAffine c R a T z))=
      (harnackAffineJacobian n R T)⁻¹*(∫ p in harnackOpen c R a T, g p) := by
  have h := (harnackAffineHomeomorph (a := a) c hR.ne' hT.ne').measurableEmbedding.integral_map
    (μ := volume.restrict (unitOpen n)) g
  change (∫ p, g p ∂Measure.map (harnackAffine c R a T) (volume.restrict (unitOpen n)))=_ at h
  rw [harnack_map_affine_open_volume c hR hT,integral_smul_measure] at h
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (harnack_affineJacobian_pos hR hT).le),
    smul_eq_mul] at h
  convert! h.symm using 1

end Yau.LeafProofs.L05Aux
