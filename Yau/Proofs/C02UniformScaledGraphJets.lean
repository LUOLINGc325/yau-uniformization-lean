import Yau.Proofs.C02CayleyNativeBridge
import Yau.Proofs.C02LinearPrecompositionJets
import Yau.Proofs.C02DilationDomains

/-! One fixed graph scale retains bounds for every coefficient jet.
The jet profile is chosen before every complex structure in the family. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}
local instance usg_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance usg_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem exists_uniform_scaled_graph_jet_bounds
    (n : ℕ) (ρ : ℝ) (b : ℕ → ℝ) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrρ : 2 * r < ρ) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧
      ∀ J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
      ContDiffOn ℝ ∞ J (Metric.ball 0 ρ) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) ρ, ‖J x - complexStructureCLM n‖ ≤ 1 / 4) →
      (∀ i x, x ∈ Metric.ball (0 : ComplexVector n) ρ → ‖iteratedFDeriv ℝ i J x‖ ≤ b i) →
      ∀ i z, z ∈ Metric.ball (0 : ComplexVector n) 2 → ∀ k l : Fin n,
      ‖iteratedFDeriv ℝ i (fun y => cayleyCoefficientMatrix (fun x => J (r • x)) y k l) z‖ ≤ c i := by
  obtain ⟨c, hc, hCayley⟩ := exists_uniform_cayley_jet_bounds n b
  refine ⟨c, hc, ?_⟩
  intro J hJ hClose hJets i z hz k l
  obtain ⟨hSmooth, hBound⟩ := hCayley _ Metric.isOpen_ball J hJ hClose hJets
  let O := (fun x : ComplexVector n => r • x) ⁻¹' Metric.ball (0 : ComplexVector n) ρ
  have hO : IsOpen O := isOpen_smul_preimage_ball r ρ
  have hzO : z ∈ O := smul_closedBall_two_mem hr hrρ (Metric.ball_subset_closedBall hz)
  have hComposition : ContDiffOn ℝ ∞
      (complexCayleyField (fun x => J (r • x))) O :=
    contDiffOn_comp_smul_preimage hSmooth r
  apply (operator_entry_jet_norm_le hO hComposition hzO i k l).trans
  have hScale := norm_iteratedFDeriv_comp_smulOn_le Metric.isOpen_ball hSmooth r z hzO i
  apply hScale.trans
  rw [abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_right (hBound i _ hzO) (pow_nonneg hr.le i)).trans
    ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1) (hc i)).trans_eq (mul_one _))

end Yau.Blueprint.C02Proof
