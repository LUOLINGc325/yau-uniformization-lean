import Yau.Proofs.C02UniformCayleyDilation
import Yau.Proofs.C02CayleyNativeBridge
import Yau.Proofs.C02NijenhuisDilation
import Yau.Proofs.C02DilationDomains

/-! A uniformly chosen dilation produces the actual native integrable
graph and finite-jet bound, including the closed receiving source ball. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ}
local instance uig_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance uig_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem exists_uniform_integrable_graph_dilation
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 2 * r < ρ ∧
      ∀ J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
      ContDiffOn ℝ ∞ J (Metric.ball 0 ρ) → J 0 = L12Aux.complexStructureCLM n →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) ρ, ∀ v, J x (J x v) = -v) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) ρ, ∀ v w, LeafCandidates.nijenhuis J x v w = 0) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) ρ, ‖J x - L12Aux.complexStructureCLM n‖ ≤ 1 / 4) →
      (∀ m x, x ∈ Metric.ball (0 : ComplexVector n) ρ → ‖iteratedFDeriv ℝ m J x‖ ≤ b m) →
      let A := cayleyCoefficientMatrix (fun y => J (r • y))
      L21Aux.MatrixSmoothOn A (Metric.ball 0 2) ∧
        L21Aux.CommutesOn A (Metric.ball 0 2) ∧
        L21Aux.JetBound q ε A (Metric.closedBall 0 2) ∧ A 0 = 0 := by
  obtain ⟨r, hr, hr1, hrρ, hSmall⟩ := exists_uniform_cayley_finiteJet_dilation n ρ hρ b q ε hε
  refine ⟨r, hr, hr1, hrρ, ?_⟩
  intro J hJ hJ0 hJ2 hN hClose hBound
  let D := fun x : ComplexVector n => r • x
  let O := D ⁻¹' Metric.ball 0 ρ
  let Jr := J ∘ D
  have hO : IsOpen O := isOpen_smul_preimage_ball r ρ
  have hJr : ContDiffOn ℝ ∞ Jr O := contDiffOn_comp_smul_preimage hJ r
  have hMap (x : ComplexVector n) (hx : x ∈ Metric.closedBall (0 : ComplexVector n) 2) : x ∈ O :=
    smul_closedBall_two_mem hr hrρ hx
  have hSquare (x : ComplexVector n) (hx : x ∈ O) (v : ComplexVector n) : Jr x (Jr x v) = -v :=
    hJ2 (D x) hx v
  have hNij (x : ComplexVector n) (hx : x ∈ O) (v w : ComplexVector n) :
      LeafCandidates.nijenhuis Jr x v w = 0 := by
    change LeafCandidates.nijenhuis (fun y => J (r • y)) x v w = 0
    rw [nijenhuis_comp_dilation J r x
      ((hJ.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)),
      hN (D x) hx v w, smul_zero]
  have hCloseR (x : ComplexVector n) (hx : x ∈ O) :
      ‖Jr x - L12Aux.complexStructureCLM n‖ ≤ 1 / 4 := hClose (D x) hx
  obtain ⟨hMatrix, hCommutes⟩ := native_cayley_graph_properties hO hJr hSquare hNij hCloseR
  have hC : ContDiffOn ℝ ∞ (complexCayleyField Jr) O := by
    intro x hx
    have he : complexCayleyField Jr = fun y => L21Aux.cayleyMap (Jr y) :=
      funext (fun y => (native_cayleyMap_eq Jr y).symm)
    rw [he]
    exact (L21Aux.contDiffAt_cayleyMap (hJr.contDiffAt (hO.mem_nhds hx))
      (by rw [native_stdComplex_eq]; exact (complex_sum_isInvertible_and_inverse_norm (Jr x) (hCloseR x hx)).1)).contDiffWithinAt
  have hBall : Metric.ball (0 : ComplexVector n) 2 ⊆ O :=
    fun x hx => hMap x (Metric.ball_subset_closedBall hx)
  refine ⟨fun i j => (hMatrix i j).mono hBall,
    fun x hx => hCommutes x (hBall hx), ?_, ?_⟩
  · intro k hk x hx i j
    exact (operator_entry_jet_norm_le hO hC (hMap x hx) k i j).trans
      (hSmall J hJ hJ0 hClose hBound k hk x hx)
  · exact cayleyCoefficientMatrix_zero (by simpa only [smul_zero] using hJ0)

end Yau.Blueprint.C02Proof
