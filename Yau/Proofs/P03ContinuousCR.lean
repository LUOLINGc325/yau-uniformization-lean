import Yau.Proofs.P03Weyl
import Yau.Proofs.P03Wirtinger
import Yau.LeafProofs.L14
import Yau.LeafProofs.L17HolomorphicRegularity

open scoped Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L14Aux

variable {n : ℕ} {U : Set (ComplexVector n)} {f : ComplexVector n → ℂ}

/-- For a continuous coefficient, the actual local weak CR equations
characterize holomorphicity of the coefficient itself. -/
theorem continuous_holomorphic_iff_weakCR (hU : IsOpen U) (hf : ContinuousOn f U) :
    DifferentiableOn ℂ f U ↔
      ∀ (i : Fin n) (ψ : ComplexVector n → ℂ),
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ z, f z * wirtBar ψ z (stdVec i) ∂lebesgueC n) = 0 := by
  constructor
  · intro hhol i ψ hψ hc hs
    have hreg := Yau.LeafProofs.L17Holomorphic.real_contDiffOn_of_complexDiff hU hhol
    have hparts := integral_compactTest_wirtBar_on hU hψ hc hs hreg (stdVec i)
    have hz : (∫ z, wirtBar f z (stdVec i) * ψ z ∂lebesgueC n) = 0 := by
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun z => by
        change wirtBar f z (stdVec i) * ψ z = 0
        by_cases hz : z ∈ U
        · rw [wirtBar_eq_zero_of_complex_differentiable f z (stdVec i)
            ((hhol z hz).differentiableAt (hU.mem_nhds hz)), zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
    rw [hz] at hparts
    exact neg_eq_zero.mp hparts.symm
  · intro hweak
    letI : IsLocallyFiniteMeasure (lebesgueC n) := by
      rw [actualMeasure_eq_volume n]
      infer_instance
    have hm : AEStronglyMeasurable f ((lebesgueC n).restrict U) :=
      hf.aestronglyMeasurable hU.measurableSet
    have hL2 (K : Set (ComplexVector n)) (hK : IsCompact K) (hKU : K ⊆ U) :
        MemLp f 2 ((lebesgueC n).restrict K) := by
      apply memLp_two_of_lintegral_norm_sq_lt_top
        ((hf.mono hKU).aestronglyMeasurable hK.measurableSet)
      have hi : IntegrableOn (fun z => ‖f z‖ ^ 2) K (lebesgueC n) :=
        (((hf.norm.pow 2).mono hKU).integrableOn_compact hK)
      exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg ‖f z‖)).mp hi.2
    obtain ⟨g, hg, heq⟩ := localCRWeyl U f hU hm hL2 hweak
    have heqOn : EqOn f g U := by
      rw [actualMeasure_eq_volume n] at heq
      exact volume.eqOn_open_of_ae_eq heq hU hf hg.continuousOn
    exact hg.congr heqOn

end Yau.NodeProofs.P03Aux
