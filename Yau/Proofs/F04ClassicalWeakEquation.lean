import Yau.Proofs.F04ClassicalDivergence

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

theorem smooth_test_integrable {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hQ : IsOpen (O ×ˢ I)) {g φ : Point n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (O ×ˢ I)) (hφ : Test (O ×ˢ I) φ) :
    Integrable (fun p => g p * φ p) (productVolume O I) := by
  have ht := test_mul_contDiffOn hQ hφ hg
  rw [dg_productVolume_eq_restrict]
  change IntegrableOn (fun p => g p * φ p) (O ×ˢ I) volume
  have hi : IntegrableOn (fun p => φ p * g p) (O ×ˢ I) volume :=
    (ht.1.continuous.integrable_of_hasCompactSupport ht.2.1).integrableOn
  convert hi using 1
  funext p
  exact mul_comm _ _

theorem classical_time_ibp {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hQ : IsOpen (O ×ˢ I)) {u φ : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) (hφ : Test (O ×ˢ I) φ) :
    (∫ p, u p * deriv (fun t => φ (p.1, t)) p.2 ∂productVolume O I) =
      -(∫ p, deriv (fun t => u (p.1, t)) p.2 * φ p ∂productVolume O I) := by
  have : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hh := smooth_local_directional_ibp (μ := (volume : Measure (Point n)))
    hQ hu hφ.1 hφ.2.1 hφ.2.2 (0, 1)
  rw [dg_productVolume_eq_restrict]
  convert hh using 1
  · apply setIntegral_congr_fun hQ.measurableSet
    intro p _
    change u p * deriv (fun t => φ (p.1, t)) p.2 = u p * fderiv ℝ φ p (0, 1)
    rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) p)]
  · congr 1
    apply setIntegral_congr_fun hQ.measurableSet
    intro p hp
    change deriv (fun t => u (p.1, t)) p.2 * φ p = fderiv ℝ u p (0, 1) * φ p
    rw [test_timeDerivative_eq_joint_fderiv ((hu.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))]

theorem classical_weak_divergence {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    (hQ : IsOpen (O ×ˢ I)) {u : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ} {R : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ I))
    (hP : ∀ i, ContDiffOn ℝ ∞ (fun p => P p i) (O ×ˢ I))
    (hR : ContDiffOn ℝ ∞ R (O ×ˢ I))
    (heq : ∀ p ∈ O ×ˢ I, deriv (fun t => u (p.1, t)) p.2 -
      (∑ i, dgGradient (fun q => P q i) p i) = R p) :
    WeakDivergenceEvolution O I u P R := by
  intro φ hφ
  have htime := classical_time_ibp hQ hu hφ
  have hspace (i : Yau.RIdx n) := classical_weakGradient hQ (hP i) φ hφ i
  have hut := smooth_test_integrable hQ hu (test_timeDerivative hφ)
  have hpt (i : Yau.RIdx n) := smooth_test_integrable hQ (hP i) (test_spatialDerivative hφ i)
  have hrt := smooth_test_integrable hQ hR hφ
  have hdi (i : Yau.RIdx n) := smooth_test_integrable hQ (dgGradient_contDiffOn hQ (hP i) i) hφ
  have hdsum : Integrable (fun p => ∑ i, dgGradient (fun q => P q i) p i * φ p)
      (productVolume O I) := integrable_finsetSum _ (fun i _ => hdi i)
  have hbalance : (∫ p, deriv (fun t => u (p.1, t)) p.2 * φ p ∂productVolume O I) =
      (∑ i, ∫ p, dgGradient (fun q => P q i) p i * φ p ∂productVolume O I) +
        ∫ p, R p * φ p ∂productVolume O I := by
    calc
      _ = ∫ p, (∑ i, dgGradient (fun q => P q i) p i * φ p) + R p * φ p ∂productVolume O I := by
        apply integral_congr_ae
        rw [dg_productVolume_eq_restrict]
        filter_upwards [ae_restrict_mem hQ.measurableSet] with p hp
        have hh := congrArg (fun t : ℝ => t * φ p) (heq p hp)
        rw [sub_mul, Finset.sum_mul] at hh
        linarith only [hh]
      _ = _ := by rw [integral_add hdsum hrt, integral_finsetSum _ (fun i _ => hdi i)]
  have hpsum : Integrable (fun p => ∑ i, P p i * d (fun x => φ (x, p.2)) p.1 i)
      (productVolume O I) := integrable_finsetSum _ (fun i _ => hpt i)
  change (∫ p, -u p * deriv (fun t => φ (p.1, t)) p.2 +
    (∑ i, P p i * d (fun x => φ (x, p.2)) p.1 i) - R p * φ p ∂productVolume O I) = 0
  simp only [neg_mul]
  have hsub := integral_sub (hut.neg.add hpsum) hrt
  have hadd := integral_add hut.neg hpsum
  simp only [Pi.add_apply, Pi.neg_apply] at hsub hadd
  rw [hsub, hadd, integral_neg, integral_finsetSum _ (fun i _ => hpt i), htime]
  simp_rw [hspace]
  rw [Finset.sum_neg_distrib]
  linarith only [hbalance]

theorem homogeneous_weak_equation {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {S : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (heq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0) :
    WeakEquation O (Ioo 0 S) a b (fun _ => 0) u (dgGradient u) := by
  have hQ := hO.prod (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) S))
  have hfields := homogeneous_classical_fields hO hsmooth hu
  have hclass := homogeneous_classical_divergence hO hsmooth hu heq
  have hFlux (i : Yau.RIdx n) :
      ContDiffOn ℝ ∞ (fun p => energyFlux a (dgGradient u) p i) (O ×ˢ Ioo 0 S) :=
    dgFlux_contDiffOn hQ hfields.1 hu i
  have hR : ContDiffOn ℝ ∞
      (fun p => ∑ i, energyDrift a b p i * dgGradient u p i) (O ×ˢ Ioo 0 S) := by
    apply ContDiffOn.sum
    intro i _
    exact (hfields.2.1 i).mul (dgGradient_contDiffOn hQ hu i)
  have hweak := classical_weak_divergence hQ hu hFlux hR
    (fun p hp => by
      have hh := hclass p hp
      rw [add_zero] at hh
      convert hh using 1
      rfl)
  intro φ hφ
  have hh := hweak φ hφ
  simpa only [zero_mul, integral_zero, energyFlux, energyDrift, Finset.sum_mul] using hh

end Yau.F04Proof
