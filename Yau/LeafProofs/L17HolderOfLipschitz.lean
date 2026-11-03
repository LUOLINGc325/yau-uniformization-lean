import Yau.LeafProofs.L17HolderEmbedding

/-! Genuine time-independent Holder elements from actual scaled Lipschitz inequalities. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem timeIndependent_weighted_difference_bound
    (P : UniformChartPartition g) {T γ L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hL : 0 ≤ L) (f : M.Carrier → ℝ)
    (hLip : ∀ p : M.Carrier, ∀ z w : ↥(ball (0 : ComplexVector n) P.radius),
      |f (P.charts.chart p w) - f (P.charts.chart p z)| ≤
        (L / P.radius) * ‖(w : ComplexVector n) - z‖)
    (i : ChartPairs P T) :
    |pairWeight P T γ i * (f (chartRight P T i).1 - f (chartLeft P T i).1)| ≤
      (3 : ℝ) ^ (1 - γ) * L := by
  let d := parabolicDistance i.2.val.1 i.2.val.2
  have hd : 0 < d := parabolicDistance_pos_of_ne i.2.property
  have hr : 0 < d / P.radius := div_pos hd P.radius_pos
  have hz : ‖(i.2.val.2.1 : ComplexVector n) - i.2.val.1.1‖ ≤ d := by
    rw [norm_sub_rev]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hb : |f (chartRight P T i).1 - f (chartLeft P T i).1| ≤ L * (d / P.radius) :=
    ((hLip i.1 i.2.val.1.1 i.2.val.2.1).trans
      (mul_le_mul_of_nonneg_left hz (div_nonneg hL P.radius_pos.le))).trans_eq (by ring)
  have heq : pairWeight P T γ i * (L * (d / P.radius)) = L * (d / P.radius) ^ (1 - γ) := by
    change (P.radius ^ γ / d ^ γ) * (L * (d / P.radius)) = L * (d / P.radius) ^ (1 - γ)
    rw [Real.rpow_sub hr, Real.rpow_one, Real.div_rpow hd.le P.radius_pos.le]
    have hdpow := (Real.rpow_pos_of_pos hd γ).ne'
    have hrpow := (Real.rpow_pos_of_pos P.radius_pos γ).ne'
    field_simp
  have hp := Real.rpow_le_rpow hr.le
    ((div_le_iff₀ P.radius_pos).mpr (parabolicDistance_le_three_radius P hT _ _))
    (sub_nonneg.mpr hγ)
  rw [abs_mul, abs_of_pos (pairWeight_pos P T γ i)]
  calc
    _ ≤ pairWeight P T γ i * (L * (d / P.radius)) :=
      mul_le_mul_of_nonneg_left hb (pairWeight_pos P T γ i).le
    _ = L * (d / P.radius) ^ (1 - γ) := heq
    _ ≤ L * (3 : ℝ) ^ (1 - γ) := mul_le_mul_of_nonneg_left hp hL
    _ = _ := mul_comm _ _

def timeIndependentElement
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : Continuous f)
    (hA : ∀ x, |f x| ≤ A)
    (hLip : ∀ p : M.Carrier, ∀ z w : ↥(ball (0 : ComplexVector n) P.radius),
      |f (P.charts.chart p w) - f (P.charts.chart p z)| ≤
        (L / P.radius) * ‖(w : ComplexVector n) - z‖) : HolderSpace P T γ :=
  ofBounds P T γ (fun q => f q.1) (hf.comp continuous_fst) A ((3 : ℝ) ^ (1 - γ) * L)
    (fun q => hA q.1) (timeIndependent_weighted_difference_bound P hT hγ hL f hLip)

theorem timeIndependentElement_value
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : Continuous f)
    (hA : ∀ x, |f x| ≤ A)
    (hLip : ∀ p : M.Carrier, ∀ z w : ↥(ball (0 : ComplexVector n) P.radius),
      |f (P.charts.chart p w) - f (P.charts.chart p z)| ≤
        (L / P.radius) * ‖(w : ComplexVector n) - z‖)
    (q : Cylinder M T) :
    holderFun (timeIndependentElement P hT hγ hL f hf hA hLip) q = f q.1 := rfl

theorem timeIndependentElement_norm_le
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hA0 : 0 ≤ A) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : Continuous f)
    (hA : ∀ x, |f x| ≤ A)
    (hLip : ∀ p : M.Carrier, ∀ z w : ↥(ball (0 : ComplexVector n) P.radius),
      |f (P.charts.chart p w) - f (P.charts.chart p z)| ≤
        (L / P.radius) * ‖(w : ComplexVector n) - z‖) :
    ‖timeIndependentElement P hT hγ hL f hf hA hLip‖ ≤ max A ((3 : ℝ) ^ (1 - γ) * L) :=
  ofBounds_norm_le P T γ _ _ _ _ hA0
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hL)
    (fun q => hA q.1) (timeIndependent_weighted_difference_bound P hT hγ hL f hLip)

end Yau.LeafProofs.L17HolderAux
