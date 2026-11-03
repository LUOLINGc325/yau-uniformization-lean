import Yau.Proofs.D02AtomDistribution
import Yau.Proofs.D02CurveComposition
import Yau.Proofs.D02LocalExtension

/-! Each temporary local extension represents the SAME limiting
distribution. Consequently every original concentration atom has zero
mass; the original regular-domain normal limit already lives on the
entire unit disc. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem regular_limit_riesz_atom_zero {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (hinj : Function.Injective F) (f : ℂ → Pt X) (u : ℂ → ℝ) (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤)
    (hdist : ∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball (0 : ℂ) 1 →
      (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z)
    (hae : (fun z => immersionPotential X.metric.form F (f z)) =ᵐ[volume.restrict (ball (0 : ℂ) 1)] u)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (regularPotentialDomain (ball (0 : ℂ) 1) μ))
    (B_F B_u : ℝ) (hBu : 0 ≤ B_u)
    (hbound : ∀ z ∈ regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ‖F (f z)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (f z) ≤ B_u)
    (henergy : (∫⁻ z in regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ENNReal.ofReal (hermitianNormSq (X.metric.form (f z)) (physicalCurveDerivative f z))) < ⊤)
    {z₀ : ℂ} (hz : z₀ ∈ ball (0 : ℂ) 1) : μ {z₀} = 0 := by
  obtain ⟨s, p, fext, hs, hU, _, hext, heq⟩ := regular_limit_local_extension X hF hImm hinj
    f μ hμ hf B_F B_u hBu hbound henergy hz
  let v : ℂ → ℝ := fun z => immersionPotential X.metric.form F (fext z)
  have hv : ContDiffOn ℝ ∞ v (ball z₀ s) := smoothFn_curve_contDiffOn
    (immersionPotential_smooth X.metric.form (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
    isOpen_ball hext
  have hextae : fext =ᵐ[volume.restrict (ball z₀ s)] f := by
    have hne : ∀ᵐ z : ℂ ∂volume, z ≠ z₀ := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_ball] with z hz0 hzU
    apply heq
    exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hz0), by simpa only [mem_ball, dist_eq_norm] using hzU⟩
  have haeU : (fun z => immersionPotential X.metric.form F (f z)) =ᵐ[volume.restrict (ball z₀ s)] u :=
    ae_restrict_of_ae_restrict_of_subset hU hae
  have hlocal : u =ᵐ[volume.restrict (ball z₀ s)] v := by
    filter_upwards [haeU, hextae] with z hz he
    change u z = immersionPotential X.metric.form F (fext z)
    rw [he]
    exact hz.symm
  exact riesz_atom_zero_of_smooth_local_representative isOpen_ball hU measurableSet_ball
    μ u v hμ hdist hv hlocal (mem_ball_self hs)

theorem regularPotentialDomain_eq_disc_of_zero_atoms (μ : Measure ℂ)
    (hzero : ∀ z ∈ ball (0 : ℂ) 1, μ {z} = 0) :
    regularPotentialDomain (ball (0 : ℂ) 1) μ = ball (0 : ℂ) 1 := by
  ext z
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, by rw [hzero z hz]; norm_num⟩⟩

end Yau.NodeProofs.D02Aux
