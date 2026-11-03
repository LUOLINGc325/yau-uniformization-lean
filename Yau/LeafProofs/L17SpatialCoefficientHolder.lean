import Yau.LeafProofs.L17ParabolicOperatorCoefficients
import Yau.LeafProofs.L17SchauderSpaceLocal

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weighted_spatial_coefficient_difference (P : UniformChartPartition g)
    {T γ C : ℝ} (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (hC : 0 ≤ C) (f : M.Carrier → ComplexVector n → F)
    (hLip : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ∀ w,
      w ∈ ball (0 : ComplexVector n) P.radius → ‖f p z-f p w‖ ≤ C*‖z-w‖)
    (i : ChartPairs P T) :
    ‖pairWeight P T γ i • (f i.1 i.2.val.2.1-f i.1 i.2.val.1.1)‖ ≤ C*(3 : ℝ)^(1-γ) := by
  let d := parabolicDistance i.2.val.1 i.2.val.2
  have hd : 0 < d := parabolicDistance_pos_of_ne i.2.property
  have hdiff : ‖f i.1 i.2.val.2.1-f i.1 i.2.val.1.1‖ ≤ C*d :=
    (hLip i.1 _ i.2.val.2.1.property _ i.2.val.1.1.property).trans
      (mul_le_mul_of_nonneg_left (by
        dsimp only [d,parabolicDistance]
        rw [norm_sub_rev]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _)) hC)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T γ i)]
  calc
    _ ≤ ((3 : ℝ)^(1-γ)*pairWeight P T 1 i)*(C*d) :=
      mul_le_mul (pairWeight_weaken_le P hTime hγ i) hdiff (norm_nonneg _)
        (mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le (pairWeight_pos P T 1 i).le)
    _ = C*(3 : ℝ)^(1-γ)*P.radius := by
      change ((3 : ℝ)^(1-γ)*(P.radius^1/d^1))*(C*d) = _
      rw [Real.rpow_one,Real.rpow_one]
      field_simp [hd.ne']
    _ ≤ _ := (mul_le_mul_of_nonneg_left hr
      (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)).trans_eq (mul_one _)

omit [NormedSpace ℝ F] in
theorem spatial_coefficient_continuous (P : UniformChartPartition g) (T : ℝ)
    (f : M.Carrier → ComplexVector n → F)
    (hf : ∀ p, ContinuousOn (f p) (ball (0 : ComplexVector n) P.radius)) :
    Continuous (fun q : LocalCylinder P T => f q.1 q.2.1) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (hf p).comp_continuous (continuous_subtype_val.comp continuous_fst)
    (fun q => q.1.property)

def spatialCoefficientHolder (P : UniformChartPartition g)
    {T γ C : ℝ} (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (hC : 0 ≤ C) (f : M.Carrier → ComplexVector n → F)
    (hf : ∀ p, ContinuousOn (f p) (ball (0 : ComplexVector n) P.radius))
    (hSup : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ‖f p z‖ ≤ C)
    (hLip : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ∀ w,
      w ∈ ball (0 : ComplexVector n) P.radius → ‖f p z-f p w‖ ≤ C*‖z-w‖) :
    LocalHolderSpace F P T γ :=
  localOfBounds F P T γ (fun q => f q.1 q.2.1) (spatial_coefficient_continuous P T f hf)
    C (C*(3 : ℝ)^(1-γ)) (fun q => hSup q.1 q.2.1 q.2.1.property)
    (weighted_spatial_coefficient_difference P hTime hγ hr hC f hLip)

theorem spatialCoefficientHolder_value (P : UniformChartPartition g)
    {T γ C : ℝ} (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (hC : 0 ≤ C) (f : M.Carrier → ComplexVector n → F)
    (hf : ∀ p, ContinuousOn (f p) (ball (0 : ComplexVector n) P.radius))
    (hSup : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ‖f p z‖ ≤ C)
    (hLip : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ∀ w,
      w ∈ ball (0 : ComplexVector n) P.radius → ‖f p z-f p w‖ ≤ C*‖z-w‖)
    (q : LocalCylinder P T) :
    localFun F (spatialCoefficientHolder P hTime hγ hr hC f hf hSup hLip) q=f q.1 q.2.1 := rfl

theorem spatialCoefficientHolder_norm_le (P : UniformChartPartition g)
    {T γ C : ℝ} (hTime : T ≤ P.radius^2) (hγ : γ ≤ 1) (hr : P.radius ≤ 1)
    (hC : 0 ≤ C) (f : M.Carrier → ComplexVector n → F)
    (hf : ∀ p, ContinuousOn (f p) (ball (0 : ComplexVector n) P.radius))
    (hSup : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ‖f p z‖ ≤ C)
    (hLip : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius → ∀ w,
      w ∈ ball (0 : ComplexVector n) P.radius → ‖f p z-f p w‖ ≤ C*‖z-w‖) :
    ‖spatialCoefficientHolder P hTime hγ hr hC f hf hSup hLip‖ ≤ C*(1+(3 : ℝ)^(1-γ)) := by
  unfold spatialCoefficientHolder
  apply (localOfBounds_norm_le F P T γ _ _ _ _ hC
    (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le) _ _).trans
  apply max_le
  · exact (le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)).trans_eq (by ring)
  · exact (le_add_of_nonneg_left hC).trans_eq (by ring)

end Yau.LeafProofs.L17Aux
