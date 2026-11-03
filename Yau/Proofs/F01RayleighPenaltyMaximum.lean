import Yau.Proofs.F01RayleighMaximumSupport
import Yau.Proofs.F01ProperPenaltyMaximum
import Yau.Proofs.F01MetricFamilySlices
import Yau.Proofs.F01SmoothContinuity

/-! The actual metric penalty is continuous and attains a maximum under
the native finite upper metric comparison supplied by a local flow. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem metricRayleighPenalty_continuousOn
    (α : HermitianField M) (hα : MetricSmooth α) (h : ℝ → HermitianField M)
    {I : Set ℝ} (hh : MetricFamilySmooth h I)
    (Q : ℝ → M.Carrier → ℝ) (hQ : ContinuousOn (fun p : M.Carrier × ℝ => Q p.2 p.1) (univ ×ˢ I))
    (hQnonneg : ∀ p : M.Carrier × ℝ, p.2 ∈ I → 0 ≤ Q p.2 p.1)
    (f : M.Carrier → ℝ) (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) :
    ContinuousOn (metricRayleighPenalty α h Q f a δ) (univ ×ˢ I) := by
  have hlog := metricFamily_logLargestRayleigh_continuousOn (fun _ => α) h
    (metricFamilySmooth_const hα I) hh
  have hlinear : ContinuousOn (fun p : M.Carrier × ℝ => a * Q p.2 p.1) (univ ×ˢ I) :=
    continuousOn_const.mul hQ
  have hJ : ContinuousOn (fun p : M.Carrier × ℝ => rayleighPenalty a (Q p.2 p.1)) (univ ×ˢ I) :=
    hlinear.add ((continuousOn_const.add hlinear).log (fun p hp => by
      have hqn := hQnonneg p hp.2
      have hpos : 0 < 1 + a * Q p.2 p.1 := by nlinarith [mul_nonneg ha hqn]
      exact hpos.ne'))
  exact (hlog.sub hJ).sub (continuousOn_const.mul (hf.comp continuous_fst).continuousOn)

theorem metricRayleighPenalty_upper
    (α : HermitianField M) (h : ℝ → HermitianField M) (I : Set ℝ)
    (Q : ℝ → M.Carrier → ℝ) (hQnonneg : ∀ p : M.Carrier × ℝ, p.2 ∈ I → 0 ≤ Q p.2 p.1)
    (f : M.Carrier → ℝ) {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D)
    (hupper : ∀ t ∈ I, ∀ x : M.Carrier,
      ((D : ℂ) • gMat α x - gMat (h t) x).PosSemidef) (δ : ℝ)
    (p : M.Carrier × ℝ) (hp : p.2 ∈ I) :
    metricRayleighPenalty α h Q f a δ p ≤ Real.log D - δ * f p.1 := by
  have hαpos := Yau.LeafProofs.L12Aux.hMat_posDef α p.1 (chartPt p.1 p.1) (mem_extChartAt_target p.1)
  have hbound : metricLargestRayleigh α (h p.2) p.1 ≤ D :=
    largestMatrixRayleigh_le_of_order hαpos hD.le (hupper p.2 hp p.1)
  have hlog := Real.log_le_log (metricLargestRayleigh_pos α (h p.2) p.1) hbound
  have hJ := rayleighPenalty_nonneg ha (hQnonneg p hp)
  unfold metricRayleighPenalty
  linarith

theorem exists_metricRayleighPenalty_max
    (α : HermitianField M) (hα : MetricSmooth α) (h : ℝ → HermitianField M)
    {I : Set ℝ} (hI : IsCompact I) (hh : MetricFamilySmooth h I)
    (Q : ℝ → M.Carrier → ℝ) (hQ : ContinuousOn (fun p : M.Carrier × ℝ => Q p.2 p.1) (univ ×ˢ I))
    (hQnonneg : ∀ p : M.Carrier × ℝ, p.2 ∈ I → 0 ≤ Q p.2 p.1)
    (f : M.Carrier → ℝ) (hf : Continuous f) (hproper : ∀ c : ℝ, IsCompact {x | f x ≤ c})
    {a D δ : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (hδ : 0 < δ)
    (hupper : ∀ t ∈ I, ∀ x : M.Carrier,
      ((D : ℂ) • gMat α x - gMat (h t) x).PosSemidef)
    (x₀ : M.Carrier) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    ∃ p : M.Carrier × ℝ, p.2 ∈ I ∧ IsMaxOn (metricRayleighPenalty α h Q f a δ) (univ ×ˢ I) p := by
  exact exists_spaceTime_max_of_proper_penalty f hproper I hI _
    (metricRayleighPenalty_continuousOn α hα h hh Q hQ hQnonneg f hf ha δ) hδ
    (metricRayleighPenalty_upper α h I Q hQnonneg f ha hD hupper δ) x₀ t₀ ht₀

theorem metricRayleighPenalty_initial_nonpos
    (α : HermitianField M) (h : ℝ → HermitianField M) (hh0 : h 0 = α)
    (Q : ℝ → M.Carrier → ℝ) (hQ : ∀ x, 0 ≤ Q 0 x)
    (f : M.Carrier → ℝ) (hf : ∀ x, 0 ≤ f x) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (x : M.Carrier) :
    metricRayleighPenalty α h Q f a δ (x, 0) ≤ 0 := by
  unfold metricRayleighPenalty
  rw [hh0, metricLargestRayleigh_self, Real.log_one]
  have hJ := rayleighPenalty_nonneg ha (hQ x)
  have hdf := mul_nonneg hδ (hf x)
  linarith

end Yau.NodeProofs.F01Aux
