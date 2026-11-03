import Yau.LeafProofs.L17BootstrapBackgroundDifferenceIdentities
import Yau.LeafProofs.L17BootstrapCompactCoefficients

/-! Genuine Hölder lifts of the selected-chart differences and normalization. -/

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
open L17Aux L17HolderAux L17SchauderAux L17SmallTranslationAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapCompactCoefficientsAux

local instance backgroundDifferenceLiftMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := backgroundDifferenceMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

/-- The three actual elements use one parameter radius and the original time interval. -/
structure BackgroundDifferences (T beta : ℝ) where
  matrixHat : ComplexVector n → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta
  logHat : ComplexVector n → LocalHolderSpace ℝ P T beta
  sigma : LocalHolderSpace ℝ P T beta
  matrix_contDiff : ContDiffOn ℝ ∞ matrixHat (ball 0 (differenceRadius D))
  log_contDiff : ContDiffOn ℝ ∞ logHat (ball 0 (differenceRadius D))
  matrix_value : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
    localFun _ (matrixHat θ).value q = matrixFamily D θ q.1 q.2.1 q.2.2
  log_value : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
    localFun ℝ (logHat θ) q = logFamily D θ q.1 q.2.1 q.2.2
  sigma_value : ∀ q : LocalCylinder P T,
    localFun ℝ sigma q = sigmaFamily D q.1 q.2.1 q.2.2
  matrix_zero : matrixHat 0 = 0
  log_zero : logHat 0 = 0
  matrix_collar : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
    q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump →
    localFun _ (matrixHat θ).value q = 0
  log_collar : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
    q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump →
    localFun ℝ (logHat θ) q = 0

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem zero_background_bounds (T : ℝ) :
    ∀ (_q : P.centers) (z : ComplexVector n), z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖(0 : F)‖ ≤ 0 ∧ ‖fderiv ℝ (fun _ : ComplexVector n => (0 : F)) z‖ ≤ 0 ∧
        ‖deriv (fun _ : ℝ => (0 : F)) t‖ ≤ 0 := by
  intros
  simp only [fderiv_const_apply,deriv_const,norm_zero,le_refl,and_self]

/-- Ordinary joint smoothness suffices; the compact lift proves all mixed budgets. -/
private theorem zero_holder_lift {T beta : ℝ}
    (hT : 0 < T) (hTime : T ≤ P.radius^2) (hb0 : 0 < beta) (hb1 : beta < 1)
    (special : ComplexVector n → ComplexVector n → ℝ → F)
    (hs : ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => special a.1 a.2.1 a.2.2)
      (specialDomain D)) :
    ∃ cHat : ComplexVector n → LocalHolderSpace F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 (differenceRadius D)) ∧
      ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
        localFun F (cHat θ) q = if q.1 = D.center then special θ q.2.1 q.2.2 else 0 :=
  exists_holder_spike_lift P D.center (differenceRadius_pos D) (differenceRadius_lt D)
    hT hTime hb0 hb1 special (fun _ _ _ => 0) hs (fun _ => contDiffOn_const)
    (A := 0) (Z := 0) (U := 0) le_rfl le_rfl le_rfl (zero_background_bounds T)

private theorem zero_banach_lift {T beta : ℝ}
    (hT : 0 < T) (hTime : T ≤ P.radius^2) (hb0 : 0 < beta) (hb1 : beta < 1)
    (special : ComplexVector n → ComplexVector n → ℝ → F)
    (hs : ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => special a.1 a.2.1 a.2.2)
      (specialDomain D)) :
    ∃ cHat : ComplexVector n → LocalHolderBanach F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 (differenceRadius D)) ∧
      ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
        localFun F (cHat θ).value q = if q.1 = D.center then special θ q.2.1 q.2.2 else 0 :=
  exists_banach_spike_lift P D.center (differenceRadius_pos D) (differenceRadius_lt D)
    hT hTime hb0 hb1 special (fun _ _ _ => 0) hs (fun _ => contDiffOn_const)
    (A := 0) (Z := 0) (U := 0) le_rfl le_rfl le_rfl (zero_background_bounds T)

/-- Actual Banach-valued parameter smoothness, literal differences, and actual σ. -/
def backgroundDifferences {T beta : ℝ} (h2rho : 2*P.radius < P.charts.radius)
    (hT : 0 < T) (hTime : T ≤ P.radius^2) (hb0 : 0 < beta) (hb1 : beta < 1) :
    BackgroundDifferences D T beta := by
  classical
  let m := Classical.choose (zero_banach_lift D hT hTime hb0 hb1 (matrixSpecial D)
    (matrixSpecial_contDiffOn D h2rho))
  have hmSpec := Classical.choose_spec (zero_banach_lift D hT hTime hb0 hb1 (matrixSpecial D)
    (matrixSpecial_contDiffOn D h2rho))
  let l := Classical.choose (zero_holder_lift D hT hTime hb0 hb1 (logSpecial D)
    (logSpecial_contDiffOn D h2rho))
  have hlSpec := Classical.choose_spec (zero_holder_lift D hT hTime hb0 hb1 (logSpecial D)
    (logSpecial_contDiffOn D h2rho))
  let s := Classical.choose (zero_holder_lift D hT hTime hb0 hb1 (normalizationSpecial D)
    (normalizationSpecial_contDiffOn D h2rho))
  have hsSpec := Classical.choose_spec (zero_holder_lift D hT hTime hb0 hb1 (normalizationSpecial D)
    (normalizationSpecial_contDiffOn D h2rho))
  have hzero : (0 : ComplexVector n) ∈ ball 0 (differenceRadius D) :=
    mem_ball_self (differenceRadius_pos D)
  have hmval : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
      localFun _ (m θ).value q = matrixFamily D θ q.1 q.2.1 q.2.2 := hmSpec.2
  have hlval : ∀ θ ∈ ball 0 (differenceRadius D), ∀ q : LocalCylinder P T,
      localFun ℝ (l θ) q = logFamily D θ q.1 q.2.1 q.2.2 := hlSpec.2
  refine ⟨m,l,s 0,hmSpec.1,hlSpec.1,hmval,hlval,hsSpec.2 0 hzero,?_,?_,?_,?_⟩
  · apply value_injective _ P T beta
    apply localFun_injective _ P T beta
    funext q
    rw [hmval 0 hzero q,matrixFamily_zero]
    rfl
  · apply localFun_injective _ P T beta
    funext q
    rw [hlval 0 hzero q,logFamily_zero]
    rfl
  · intro θ hθ q hq
    rw [hmval θ hθ q]
    exact matrixFamily_collar D θ q.1 q.2.1 q.2.2 hq
  · intro θ hθ q hq
    rw [hlval θ hθ q]
    exact logFamily_collar D θ q.1 q.2.1 q.2.2 hq

end Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
