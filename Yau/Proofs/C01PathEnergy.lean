import Yau.Proofs.C01SmoothSegmentLength
import Yau.Proofs.C01RealTangentRicciJets

/-! The exact energy of a genuine globally smooth path bounds the
squared project distance by Cauchy--Schwarz. The elementary unit-interval
integral proof follows canonical Ae0dbe L23LocalDistanceSupportEnergy;
no project energy or completeness API is imported. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

theorem unit_interval_integral_sq_le {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1))
    (hf2 : IntegrableOn (fun s => f s ^ 2) (Set.Icc (0 : ℝ) 1)) :
    (∫ s in Set.Icc (0 : ℝ) 1, f s)^2 ≤ ∫ s in Set.Icc (0 : ℝ) 1, f s ^ 2 := by
  let L := ∫ s in Set.Icc (0 : ℝ) 1, f s
  have hconst : IntegrableOn (fun _ : ℝ => L^2) (Set.Icc (0 : ℝ) 1) := integrableOn_const (hs := by simp)
  have heq : (fun s => (f s-L)^2) = (fun s => f s^2-(2*L)*f s+L^2) := by
    funext s
    ring
  have H : 0 ≤ ∫ s in Set.Icc (0 : ℝ) 1, (f s-L)^2 := integral_nonneg fun _ => sq_nonneg _
  rw [heq] at H
  have hlinear : IntegrableOn (fun s => f s^2-(2*L)*f s) (Set.Icc (0 : ℝ) 1) :=
    hf2.sub (hf.const_mul (2*L))
  have hadd : (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s+L^2) =
      (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s) +
        ∫ s in Set.Icc (0 : ℝ) 1, L^2 := integral_add hlinear hconst
  have hsub : (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s) =
      (∫ s in Set.Icc (0 : ℝ) 1, f s^2) -
        ∫ s in Set.Icc (0 : ℝ) 1, (2*L)*f s := integral_sub hf2 (hf.const_mul (2*L))
  rw [hadd,hsub,integral_const_mul] at H
  simp only [integral_const,smul_eq_mul] at H
  norm_num [Measure.real] at H
  change 0 ≤ (∫ s in Set.Icc (0 : ℝ) 1, f s^2) - (2*L)*L + L^2 at H
  change L^2 ≤ ∫ s in Set.Icc (0 : ℝ) 1, f s^2
  nlinarith only [H]

variable {n : ℕ} {M : ComplexManifold n}

def actualPathEnergy (k : HermitianField M) (f : ℝ → M.Carrier) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1, actualPathSpeed k f u ^ 2

theorem actualPathSpeed_sq (k : HermitianField M) (f : ℝ → M.Carrier) (u : ℝ) :
    actualPathSpeed k f u ^ 2 = realTangentSpeedSq k (f u) (realCurveVelocity f u) :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _))

theorem actualPathSpeed_continuous (k : HermitianField M) (hk : MetricSmooth k)
    (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f → Continuous (actualPathSpeed k f) := by
  letI := manifold_realSmooth M
  intro hf
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  have heq : actualPathSpeed k f = (fun u => ‖realCurveVelocity f u‖) := by
    funext u
    rw [underlyingRealTangent_norm]
    rfl
  rw [heq]
  exact continuous_norm_realCurveVelocity k hk hf

theorem distance_sq_le_actualPathEnergy
    (k : HermitianField M) (hk : MetricSmooth k) (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ∀ hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f,
      inducedDistance k (f 0) (f 1) ^ 2 ≤ actualPathEnergy k f := by
  letI := manifold_realSmooth M
  intro hf
  have hc := actualPathSpeed_continuous k hk f hf
  have hi : IntegrableOn (actualPathSpeed k f) (Set.Icc (0 : ℝ) 1) volume :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hi₂ : IntegrableOn (fun u => actualPathSpeed k f u ^ 2) (Set.Icc (0 : ℝ) 1) volume :=
    (hc.pow 2).continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hEL : actualPathELength k f 0 1 = ENNReal.ofReal (∫ u in Set.Icc (0 : ℝ) 1, actualPathSpeed k f u) := by
    rw [actualPathELength_eq_lintegral]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _)).symm
  have hD := distance_le_smooth_segment_length k hk f hf 0 1 zero_le_one
  rw [hEL] at hD
  have hnonneg : 0 ≤ ∫ u in Set.Icc (0 : ℝ) 1, actualPathSpeed k f u :=
    integral_nonneg fun _ => Real.sqrt_nonneg _
  have hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hD
  exact ((sq_le_sq₀ (inducedDistance_nonneg k hk _ _) hnonneg).mpr hreal).trans
    (unit_interval_integral_sq_le hi hi₂)

theorem actualPathEnergy_eq_of_constant_speedSq
    (k : HermitianField M) (f : ℝ → M.Carrier) (D : ℝ)
    (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1, realTangentSpeedSq k (f u) (realCurveVelocity f u) = D) :
    actualPathEnergy k f = D := by
  have HE : actualPathEnergy k f = ∫ _u in Set.Icc (0 : ℝ) 1, D := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [actualPathSpeed_sq]
    exact hD u hu
  simpa [integral_const, Measure.real] using HE

end Yau.NodeProofs.C01Aux
