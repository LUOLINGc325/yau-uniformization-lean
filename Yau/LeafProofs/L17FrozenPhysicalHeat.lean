import Yau.LeafProofs.L17FrozenGaussianHeat
import Yau.LeafProofs.L17ParabolicJetScaling

/-! The actual radius-scaled frozen Gaussian equation and its four true local jets. -/

noncomputable section

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def parabolicSourceRescale (ρ : ℝ) (f : Point n → ℝ) (q : Point n) : ℝ :=
  f (ρ • q.1, ρ ^ 2 * q.2)

theorem parabolicSourceRescale_scalePoint {ρ : ℝ} (hρ : ρ ≠ 0)
    (f : Point n → ℝ) (q : Point n) :
    parabolicSourceRescale ρ f (parabolicScalePoint ρ q) = f q := by
  apply congrArg f
  apply Prod.ext
  · exact smul_inv_smul₀ hρ q.1
  · change ρ ^ 2 * ((ρ ^ 2)⁻¹ * q.2) = q.2
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hρ), one_mul]

theorem linearOp_parabolicUnscale_const {ρ T : ℝ} (hρ : ρ ≠ 0) (hT : 0 < T)
    {u : Point n → ℝ} (hu : C2 (cylinder Set.univ 0 (T / ρ ^ 2)) u)
    (a : Mat n) {q : Point n} (hq : q ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) (fun _ => a) (fun _ _ => 0) (parabolicUnscale ρ u) q =
      linearOp (cylinder Set.univ 0 (T / ρ ^ 2)) (fun _ => a) (fun _ _ => 0) u
        (parabolicScalePoint ρ q) := by
  simp only [linearOp, timeD_parabolicUnscale hρ hT hu hq,
    spatialDD_parabolicUnscale hρ, zero_mul, Finset.sum_const_zero, sub_zero]
  rfl

def BoundedChartFamily.frozenPhysicalHeat (A : BoundedChartFamily g) (ρ : ℝ) (p : M.Carrier)
    (f : Point n → ℝ) : Point n → ℝ :=
  parabolicUnscale ρ (A.frozenHeatDuhamel p (parabolicSourceRescale ρ f))

theorem BoundedChartFamily.frozenPhysicalHeat_initial
    (A : BoundedChartFamily g) (ρ : ℝ) (p : M.Carrier) (f : Point n → ℝ) (x : Space n) :
    A.frozenPhysicalHeat ρ p f (x, 0) = 0 := by
  simp only [BoundedChartFamily.frozenPhysicalHeat, parabolicUnscale, mul_zero,
    BoundedChartFamily.frozenHeatDuhamel_initial]

theorem BoundedChartFamily.frozenPhysicalHeat_equation
    (A : BoundedChartFamily g) {ρ T α F : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (hSmall : T ≤ ρ ^ 2) (hα : 0 < α) (hα1 : α < 1)
    (p : M.Carrier) {f : Point n → ℝ}
    (hf : HolderBound α (cylinder Set.univ 0 (T / ρ ^ 2)) (parabolicSourceRescale ρ f) F)
    {q : Point n} (hq : q ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T)
      (fun _ => scalarSymbol (pullbackMatrix g (A.chart p) 0)) (fun _ _ => 0)
      (A.frozenPhysicalHeat ρ p f) q = f q := by
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hS : 0 < T / ρ ^ 2 := div_pos hT hsq
  have hSone : T / ρ ^ 2 ≤ 1 := (div_le_one hsq).mpr hSmall
  obtain ⟨K, _, hbound⟩ := A.frozenHeatDuhamel_controlled_bounds hα hα1
  have hu := hbound p (T / ρ ^ 2) F hS hSone (parabolicSourceRescale ρ f) hf
  unfold BoundedChartFamily.frozenPhysicalHeat
  rw [linearOp_parabolicUnscale_const hρ.ne' hT hu.1.1 _ hq]
  rw [A.frozenHeatDuhamel_equation p hα hα1 hS hSone hf
    (parabolicScalePoint_mem_cylinder hρ.ne' hq)]
  exact parabolicSourceRescale_scalePoint hρ.ne' f q

theorem BoundedChartFamily.frozenPhysicalHeat_controlled_jets
    (A : BoundedChartFamily g) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ : ℝ) (p : M.Carrier) (T F : ℝ), 0 < ρ → 0 < T → T ≤ ρ ^ 2 →
      ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 (T / ρ ^ 2)) (parabolicSourceRescale ρ f) F →
      let J := K * F * ((T / ρ ^ 2) ^ (1 / 2 : ℝ) + (T / ρ ^ 2) ^ ((1 - α) / 2))
      C2 (cylinder Set.univ 0 T) (A.frozenPhysicalHeat ρ p f) ∧
      (∀ q ∈ cylinder Set.univ 0 T,
        |A.frozenPhysicalHeat ρ p f q| ≤ ρ ^ 2 * J ∧
        ‖spatialD (A.frozenPhysicalHeat ρ p f) q‖ ≤ ρ * J ∧
        ‖spatialDD (A.frozenPhysicalHeat ρ p f) q‖ ≤ K * F ∧
        |timeD (cylinder Set.univ 0 T) (A.frozenPhysicalHeat ρ p f) q| ≤ K * F) ∧
      ∀ q ∈ cylinder Set.univ 0 T, ∀ r ∈ cylinder Set.univ 0 T,
        |A.frozenPhysicalHeat ρ p f q - A.frozenPhysicalHeat ρ p f r| ≤
          (2 * ρ ^ 2 * J) * (parabolicDistance q r / ρ) ^ α ∧
        ‖spatialD (A.frozenPhysicalHeat ρ p f) q - spatialD (A.frozenPhysicalHeat ρ p f) r‖ ≤
          (2 * ρ * J) * (parabolicDistance q r / ρ) ^ α ∧
        ‖spatialDD (A.frozenPhysicalHeat ρ p f) q - spatialDD (A.frozenPhysicalHeat ρ p f) r‖ ≤
          (2 * (K * F)) * (parabolicDistance q r / ρ) ^ α ∧
        |timeD (cylinder Set.univ 0 T) (A.frozenPhysicalHeat ρ p f) q -
          timeD (cylinder Set.univ 0 T) (A.frozenPhysicalHeat ρ p f) r| ≤
          (2 * (K * F)) * (parabolicDistance q r / ρ) ^ α := by
  obtain ⟨K, hK, hbound⟩ := A.frozenHeatDuhamel_controlled_bounds hα hα1
  refine ⟨K, hK, ?_⟩
  intro ρ p T F hρ hT hSmall f hf
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hS : 0 < T / ρ ^ 2 := div_pos hT hsq
  have hSone : T / ρ ^ 2 ≤ 1 := (div_le_one hsq).mpr hSmall
  have h := hbound p (T / ρ ^ 2) F hS hSone (parabolicSourceRescale ρ f) hf
  exact parabolicUnscale_four_jet_bounds hρ hT hα.le h.1 h.2.2

end Yau.LeafProofs.L17Aux
