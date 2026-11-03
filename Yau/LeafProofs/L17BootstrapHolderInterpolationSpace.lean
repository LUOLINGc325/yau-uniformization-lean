import Yau.LeafProofs.L17BootstrapHolderInterpolationReal
import Yau.LeafProofs.L17SchauderEmbedding

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapHolderInterpolationAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem pairWeight_eq_inv_scaled_rpow (P : UniformChartPartition g) (T gamma : ℝ)
    (i : ChartPairs P T) :
    pairWeight P T gamma i =
      ((parabolicDistance i.2.val.1 i.2.val.2/P.radius)^gamma)⁻¹ := by
  unfold pairWeight scaledPairWeight
  rw [Real.div_rpow (parabolicDistance_pos_of_ne i.2.property).le P.radius_pos.le,inv_div]

theorem weighted_norm_eq_scaled_quotient {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) (T gamma : ℝ) (i : ChartPairs P T) (v : F) :
    ‖pairWeight P T gamma i • v‖ =
      ‖v‖/(parabolicDistance i.2.val.1 i.2.val.2/P.radius)^gamma := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T gamma i),
    pairWeight_eq_inv_scaled_rpow]
  simp only [div_eq_mul_inv,mul_comm]

theorem weighted_pair_interpolation_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) {T alpha beta S H : ℝ}
    (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (f : LocalCylinder P T → F) (hSup : ∀ q, ‖f q‖ ≤ S) (i : ChartPairs P T)
    (hAlpha : ‖pairWeight P T alpha i • (f (localRight P T i)-f (localLeft P T i))‖ ≤ H) :
    ‖pairWeight P T beta i • (f (localRight P T i)-f (localLeft P T i))‖ ≤
      interpolationBudget alpha beta S H := by
  have hd : 0 < parabolicDistance i.2.val.1 i.2.val.2/P.radius :=
    div_pos (parabolicDistance_pos_of_ne i.2.property) P.radius_pos
  rw [weighted_norm_eq_scaled_quotient] at hAlpha ⊢
  apply scalar_interpolation_quotient_bound hba hS hH hd (norm_nonneg _)
    ((norm_sub_le _ _).trans (by linarith [hSup (localRight P T i),hSup (localLeft P T i)]))
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hd alpha)).mp hAlpha

theorem localWeaken_norm_le_interpolation {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : UniformChartPartition g) {T alpha beta S H : ℝ} (hT : T ≤ P.radius^2)
    (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (u : LocalHolderSpace F P T alpha) (hSup : ∀ q, ‖localFun F u q‖ ≤ S) (hNorm : ‖u‖ ≤ H) :
    ‖localWeakenElement F P hT hba.2.le u‖ ≤ max S (interpolationBudget alpha beta S H) := by
  apply (localNorm_le_iff F _ (hS.trans (le_max_left _ _))).mpr
  constructor
  · intro q
    exact (hSup q).trans (le_max_left _ _)
  · intro i
    exact (weighted_pair_interpolation_bound P hba hS hH (localFun F u) hSup i
      ((localWeighted_difference_norm_le F u i).trans hNorm)).trans (le_max_right _ _)

theorem holderWeaken_norm_le_interpolation
    (P : UniformChartPartition g) {T alpha beta S H : ℝ} (hT : T ≤ P.radius^2)
    (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (u : HolderSpace P T alpha) (hSup : ∀ q, |holderFun u q| ≤ S) (hNorm : ‖u‖ ≤ H) :
    ‖weakenElement P hT hba.2.le u‖ ≤ max S (interpolationBudget alpha beta S H) := by
  apply (L17HolderAux.norm_le_iff _ (hS.trans (le_max_left _ _))).mpr
  constructor
  · intro q
    exact (hSup q).trans (le_max_left _ _)
  · intro i
    have h := weighted_pair_interpolation_bound P hba hS hH
      (fun q : LocalCylinder P T => holderFun u (chartPoint P T q.1 q.2))
      (fun q => by simpa only [Real.norm_eq_abs] using hSup (chartPoint P T q.1 q.2)) i
      (by simpa only [Real.norm_eq_abs,smul_eq_mul,localRight,localLeft,chartRight,chartLeft] using
        (weighted_difference_abs_le_norm u i).trans hNorm)
    exact (show |pairWeight P T beta i*(holderFun u (chartRight P T i)-holderFun u (chartLeft P T i))| ≤
      interpolationBudget alpha beta S H by simpa only [Real.norm_eq_abs,smul_eq_mul,localRight,localLeft,chartRight,chartLeft] using h).trans
        (le_max_right _ _)

theorem schauderWeaken_norm_le_interpolation_raw
    (P : UniformChartPartition g) {T alpha beta S H : ℝ} {hpos : 0 < T}
    (hT : T ≤ P.radius^2) (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (u : SchauderSpace P T alpha hpos)
    (hSup0 : ∀ q, |holderFun u.val.1.1 q| ≤ S)
    (hSup1 : ∀ q, ‖localFun (D1 n) u.val.1.2 q‖ ≤ S)
    (hSup2 : ∀ q, ‖localFun (D2 n) u.val.2.1 q‖ ≤ S)
    (hSup3 : ∀ q, |holderFun u.val.2.2 q| ≤ S) (hNorm : ‖u‖ ≤ H) :
    ‖schauderWeakenCLM P hpos hT hba.2.le u‖ ≤ max S (interpolationBudget alpha beta S H) := by
  have h0 : ‖u.val.1.1‖ ≤ H := ((le_max_left _ _).trans (le_max_left _ _)).trans hNorm
  have h1 : ‖u.val.1.2‖ ≤ H := ((le_max_right _ _).trans (le_max_left _ _)).trans hNorm
  have h2 : ‖u.val.2.1‖ ≤ H := ((le_max_left _ _).trans (le_max_right _ _)).trans hNorm
  have h3 : ‖u.val.2.2‖ ≤ H := ((le_max_right _ _).trans (le_max_right _ _)).trans hNorm
  change max (max ‖weakenElement P hT hba.2.le u.val.1.1‖
    ‖localWeakenElement (D1 n) P hT hba.2.le u.val.1.2‖)
    (max ‖localWeakenElement (D2 n) P hT hba.2.le u.val.2.1‖
      ‖weakenElement P hT hba.2.le u.val.2.2‖) ≤ _
  exact max_le
    (max_le (holderWeaken_norm_le_interpolation P hT hba hS hH _ hSup0 h0)
      (localWeaken_norm_le_interpolation P hT hba hS hH _ hSup1 h1))
    (max_le (localWeaken_norm_le_interpolation P hT hba hS hH _ hSup2 h2)
      (holderWeaken_norm_le_interpolation P hT hba hS hH _ hSup3 h3))

theorem schauderWeaken_norm_le_interpolation
    (P : UniformChartPartition g) {T alpha beta S H : ℝ} {hpos : 0 < T}
    (hT : T ≤ P.radius^2) (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (u : SchauderSpace P T alpha hpos)
    (hSup0 : ∀ q, (P.radius^2)⁻¹*|schauderFun u q| ≤ S)
    (hSup1 : ∀ q, P.radius⁻¹*‖gradientFun u q‖ ≤ S)
    (hSup2 : ∀ q, ‖hessianFun u q‖ ≤ S)
    (hSup3 : ∀ q, |timeFun u q| ≤ S) (hNorm : ‖u‖ ≤ H) :
    ‖schauderWeakenCLM P hpos hT hba.2.le u‖ ≤ max S (interpolationBudget alpha beta S H) := by
  apply schauderWeaken_norm_le_interpolation_raw P hT hba hS hH u _ _ hSup2 hSup3 hNorm
  · intro q
    have h := hSup0 q
    change (P.radius^2)⁻¹*|P.radius^2*holderFun u.val.1.1 q| ≤ S at h
    rw [abs_mul,abs_of_pos (pow_pos P.radius_pos 2),← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 P.radius_pos.ne'),one_mul] at h
    exact h
  · intro q
    have h := hSup1 q
    change P.radius⁻¹*‖P.radius • localFun (D1 n) u.val.1.2 q‖ ≤ S at h
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos,← mul_assoc,
      inv_mul_cancel₀ P.radius_pos.ne',one_mul] at h
    exact h

theorem schauder_embedding_preserves_actual_jets
    (P : UniformChartPartition g) {T alpha beta : ℝ} (hpos : 0 < T)
    (hT : T ≤ P.radius^2) (hba : beta ≤ alpha) (u : SchauderSpace P T alpha hpos) :
    schauderFun (schauderWeakenCLM P hpos hT hba u)=schauderFun u ∧
    gradientFun (schauderWeakenCLM P hpos hT hba u)=gradientFun u ∧
    hessianFun (schauderWeakenCLM P hpos hT hba u)=hessianFun u ∧
    timeFun (schauderWeakenCLM P hpos hT hba u)=timeFun u := ⟨rfl,rfl,rfl,rfl⟩

theorem alphaBetaSchauderEmbedding_quarter_bound
    (P : UniformChartPartition g) {T A eps : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius^2)
    (hA : 0 ≤ A) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (u : SchauderSpace P T (1/2) hpos)
    (hSup0 : ∀ q, (P.radius^2)⁻¹*|schauderFun u q| ≤ A*eps^(1/2 : ℝ))
    (hSup1 : ∀ q, P.radius⁻¹*‖gradientFun u q‖ ≤ A*eps^(1/2 : ℝ))
    (hSup2 : ∀ q, ‖hessianFun u q‖ ≤ A*eps^(1/2 : ℝ))
    (hSup3 : ∀ q, |timeFun u q| ≤ A*eps^(1/2 : ℝ)) (hNorm : ‖u‖ ≤ 2*A) :
    ‖alphaBetaSchauderEmbedding P hpos hT u‖ ≤ 4*A*eps^(1/4 : ℝ) := by
  have h := schauderWeaken_norm_le_interpolation P hT (by norm_num : 0<(1/4 : ℝ) ∧ (1/4 : ℝ)<1/2)
    (mul_nonneg hA (Real.rpow_nonneg heps _)) (mul_nonneg (by norm_num) hA)
    u hSup0 hSup1 hSup2 hSup3 hNorm
  exact h.trans (half_quarter_budget_le hA heps heps1)

end Yau.LeafProofs.L17BootstrapHolderInterpolationAux
