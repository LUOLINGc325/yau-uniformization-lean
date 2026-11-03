import Yau.Proofs.D05SmoothDual

/-! A holomorphic ambient dual of a nowhere-zero holomorphic vector on a
smaller disc. All scalar correction entries use the same constructed operator. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

variable {ι : Type*} [Fintype ι]

def correctionSolution (e : ℂ → ι → ℂ) (χ : ℂ → ℝ) (z : ℂ) (j k : ι) : ℂ :=
  cutoffDbarSolution χ (fun w => dualCorrection e w j k) z

def holomorphicDualCandidate (e : ℂ → ι → ℂ) (χ : ℂ → ℝ) (z : ℂ) (k : ι) : ℂ :=
  smoothDual e z k - ∑ j, e z j * correctionSolution e χ z j k

theorem correctionSolution_smooth {U : Set ℂ} (hU : IsOpen U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) (j k : ι) :
    ContDiff ℝ ∞ (fun z => correctionSolution e χ z j k) :=
  cutoffDbarSolution_smooth hU (dualCorrection_contDiffOn hU he hne j k) hχ hsχ hcχ

theorem correctionSolution_antisymm {U : Set ℂ} (hU : IsOpen U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) (z : ℂ) (j k : ι) :
    correctionSolution e χ z j k = -correctionSolution e χ z k j := by
  have hswap : (fun w => dualCorrection e w j k) =
      fun w => -dualCorrection e w k j := funext fun w => dualCorrection_antisymm e w j k
  unfold correctionSolution
  rw [hswap, cutoffDbarSolution_neg hU (dualCorrection_contDiffOn hU he hne k j)
    hχ hsχ hcχ]

theorem antisymmetric_double_contraction (v : ι → ℂ) (C : ι → ι → ℂ)
    (hC : ∀ j k, C j k = -C k j) :
    ∑ k, v k * ∑ j, v j * C j k = 0 := by
  let T := ∑ k, ∑ j, v k * v j * C j k
  have hT : T = -T := by
    calc
      T = ∑ j, ∑ k, v k * v j * C j k := Finset.sum_comm
      _ = ∑ j, ∑ k, -(v j * v k * C k j) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        calc
          v k * v j * C j k = v k * v j * (-C k j) :=
            congrArg (fun t => v k * v j * t) (hC j k)
          _ = -(v j * v k * C k j) := by ring
      _ = -T := by simp only [T, Finset.sum_neg_distrib]
  have hzero : T = 0 := by
    linear_combination (1 / 2 : ℂ) * hT
  simpa only [T, Finset.mul_sum, mul_assoc] using hzero

theorem holomorphicDualCandidate_pairing {U : Set ℂ} (hU : IsOpen U)
    {e : ℂ → ι → ℂ} (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) {z : ℂ} (hz : z ∈ U) :
    ∑ k, e z k * holomorphicDualCandidate e χ z k = 1 := by
  simp only [holomorphicDualCandidate, mul_sub, Finset.sum_sub_distrib]
  rw [smoothDual_pairing (hne z hz),
    antisymmetric_double_contraction (e z) (correctionSolution e χ z)
      (correctionSolution_antisymm hU he hne hχ hsχ hcχ z)]
  ring

theorem holomorphicDualCandidate_smooth {U : Set ℂ} (hU : IsOpen U)
    {e : ℂ → ι → ℂ} (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) (k : ι) :
    ContDiffOn ℝ ∞ (fun z => holomorphicDualCandidate e χ z k) U := by
  exact (smoothDual_contDiffOn he hne k).sub (ContDiffOn.sum fun j _ =>
    ((he j).restrict_scalars ℝ).mul
      ((correctionSolution_smooth hU he hne hχ hsχ hcχ j k).contDiffOn))

theorem wirtBar_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    wirtBar (fun w => f w - g w) z v = wirtBar f z v - wirtBar g z v := by
  simp only [wirtBar, fderiv_fun_sub hf hg, sub_apply]
  ring

theorem holomorphicDualCandidate_holomorphic {U V : Set ℂ} (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ)
    (hχone : ∀ z ∈ V, χ z = 1) (k : ι) :
    ContDiffOn ℂ ∞ (fun z => holomorphicDualCandidate e χ z k) V := by
  apply V03Proof.complex_holomorphic_contDiffOn hV
  intro z hz
  have hzU := hVU hz
  have hde (j : ι) : DifferentiableAt ℂ (fun w => e w j) z :=
    ((he j z hzU).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  have hdℓ : DifferentiableAt ℝ (fun w => smoothDual e w k) z :=
    ((smoothDual_contDiffOn he hne k z hzU).contDiffAt
      (hU.mem_nhds hzU)).differentiableAt (by simp)
  have hdcR (j : ι) : DifferentiableAt ℝ (fun w => correctionSolution e χ w j k) z :=
    (correctionSolution_smooth hU he hne hχ hsχ hcχ j k).contDiffAt.differentiableAt (by simp)
  have hdc (j : ι) : wirtBar (fun w => correctionSolution e χ w j k) z 1 =
      dualCorrection e z j k :=
    cutoffDbarSolution_dbar hU (dualCorrection_contDiffOn hU he hne j k)
      hχ hsχ hcχ (hχone z hz)
  have hsum : DifferentiableAt ℝ
      (fun w => ∑ j, e w j * correctionSolution e χ w j k) z := by
    exact DifferentiableAt.fun_sum (fun j _ => ((hde j).restrictScalars ℝ).fun_mul (hdcR j))
  apply (differentiableAt_of_wirtBar_zero (hdℓ.sub hsum) ?_).differentiableWithinAt
  change wirtBar (fun w => smoothDual e w k -
    ∑ j, e w j * correctionSolution e χ w j k) z 1 = 0
  rw [wirtBar_sub hdℓ hsum, V03Proof.wirtBar_sum Finset.univ
    (fun j w => e w j * correctionSolution e χ w j k) z 1
    (fun j _ => ((hde j).restrictScalars ℝ).mul (hdcR j))]
  simp only [V03Proof.wirtBar_mul ((hde _).restrictScalars ℝ) (hdcR _),
    V03Proof.wirtBar_holomorphic (hde _), zero_mul, zero_add, hdc]
  rw [dualCorrection_contraction hU he hne hzU]
  ring

theorem ambient_holomorphic_dual_of_nonvanishing {e : ℂ → ι → ℂ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) (Metric.ball 0 R))
    (hne : ∀ z ∈ Metric.ball (0 : ℂ) R, e z ≠ 0) :
    ∃ a : ℂ → ι → ℂ,
      (∀ k, ContDiffOn ℂ ∞ (fun z => a z k) (Metric.ball 0 ρ)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∑ k, e z k * a z k = 1 := by
  obtain ⟨χ, hχ, hcχ, hsχ, hχone⟩ := disc_cutoff_exists hρ hρR
  refine ⟨holomorphicDualCandidate e χ,
    holomorphicDualCandidate_holomorphic Metric.isOpen_ball Metric.isOpen_ball
      (Metric.ball_subset_ball hρR.le) he hne hχ hsχ hcχ
      (fun z hz => hχone z (Metric.ball_subset_closedBall hz)), ?_⟩
  exact fun z hz => holomorphicDualCandidate_pairing Metric.isOpen_ball he hne
    hχ hsχ hcχ (Metric.ball_subset_ball hρR.le hz)

end Yau.Blueprint.D05Proof
