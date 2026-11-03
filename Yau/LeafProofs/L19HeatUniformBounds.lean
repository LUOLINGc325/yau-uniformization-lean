import Yau.LeafProofs.L19HeatInitial
import Yau.LeafProofs.L19HeatMarkovPositivity
import Mathlib.Analysis.Convex.Integral

/-! Uniform scalar bounds for actual L² Bochner integrals and compact
heat initial values, without an L² constant function. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def lpUniformBound {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℝ) : Set (Lp ℝ 2 μ) :=
  {f | ∀ᵐ x ∂μ, |f x| ≤ K}

theorem lpUniformBound_isClosed {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : ℝ) (hK : 0 ≤ K) : IsClosed (lpUniformBound μ K) := by
  let F : Lp ℝ 2 μ → Lp ℝ 2 μ := fun f => Lp.posPart f + Lp.negPart f
  have hF (f : Lp ℝ 2 μ) : F f =ᵐ[μ] fun x => |f x| := by
    filter_upwards [Lp.coeFn_add (Lp.posPart f) (Lp.negPart f),
      Lp.coeFn_posPart f, Lp.coeFn_negPart f] with x hs hp hn
    change (Lp.posPart f + Lp.negPart f) x = _
    rw [hs, Pi.add_apply, hp, hn]
    rcases le_total (f x) 0 with hf | hf
    · rw [max_eq_right hf, min_eq_left hf, abs_of_nonpos hf]
      ring
    · rw [max_eq_left hf, min_eq_right hf, abs_of_nonneg hf]
      ring
  have hEq : lpUniformBound μ K = F ⁻¹'
      {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K} := by
    ext f
    constructor
    · intro hf
      filter_upwards [hf, hF f] with x hx hax
      rw [hax]
      exact ⟨abs_nonneg _, hx⟩
    · intro hf
      filter_upwards [hf, hF f] with x hx hax
      rw [hax] at hx
      exact hx.2
  rw [hEq]
  exact (normalIntervalL2_isClosed μ K hK).preimage (Lp.continuous_posPart.add Lp.continuous_negPart)

theorem lpUniformBound_convex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : ℝ) : Convex ℝ (lpUniformBound μ K) := by
  intro f hf k hk a b ha hb hab
  filter_upwards [hf, hk, Lp.coeFn_add (a • f) (b • k),
    Lp.coeFn_smul a f, Lp.coeFn_smul b k] with x hfx hkx hsum haf hbk
  rw [hsum, Pi.add_apply, haf, hbk, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  calc
    |a * f x + b * k x| ≤ |a * f x| + |b * k x| := abs_add_le _ _
    _ = a * |f x| + b * |k x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * K + b * K := add_le_add (mul_le_mul_of_nonneg_left hfx ha)
      (mul_le_mul_of_nonneg_left hkx hb)
    _ = K := by rw [← add_mul, hab, one_mul]

theorem lp_interval_integral_uniform_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    {F : ℝ → Lp ℝ 2 μ} (hFI : IntervalIntegrable F volume 0 T)
    (hF : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ᵐ x ∂μ, |F t x| ≤ K) :
    ∀ᵐ x ∂μ, |(∫ t in (0 : ℝ)..T, F t) x| ≤ T * K := by
  have hI0 : volume (Set.Ioc (0 : ℝ) T) ≠ 0 := by
    rw [Real.volume_Ioc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hT).ne'
  have hItop : volume (Set.Ioc (0 : ℝ) T) ≠ ⊤ := by simp
  have hFAE : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) T), F t ∈ lpUniformBound μ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hF t ht
  have hAvg := (lpUniformBound_convex μ K).set_average_mem (lpUniformBound_isClosed μ K hK)
    hI0 hItop hFAE ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hFI)
  have hAvg' : ∀ᵐ x ∂μ, |(T⁻¹ • (∫ t in (0 : ℝ)..T, F t)) x| ≤ K := by
    have hvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by simp [Real.volume_Ioc, hT.le]
    rw [setAverage_eq, hvol, ← intervalIntegral.integral_of_le hT.le] at hAvg
    exact hAvg
  filter_upwards [hAvg', Lp.coeFn_smul T⁻¹ (∫ t in (0 : ℝ)..T, F t)] with x hx hsmul
  rw [hsmul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hT)] at hx
  calc
    |(∫ t in (0 : ℝ)..T, F t) x| = T * (T⁻¹ * |(∫ t in (0 : ℝ)..T, F t) x|) := by field_simp
    _ ≤ T * K := mul_le_mul_of_nonneg_left hx hT.le

variable {n : ℕ} {M : ComplexManifold n}

/-- Compact smooth initial data have the true uniform first-order initial
bound in the actual scalar L² classes. -/
theorem scalarHeat_compact_initial_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {K T : ℝ} (hK0 : 0 ≤ K) (hT : 0 < T)
    (hLap : ∀ x, |laplacian g.form k x| ≤ K) :
    ∀ᵐ x ∂μ, |scalarHeatFamily g μ hμ T (scalarEnergyDomainL2 g μ hμ k) x - k x| ≤ T * K := by
  have hL : ∀ᵐ x ∂μ, |scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k) x| ≤ K := by
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ (scalarCompactLaplacian g μ hμ k)] with x hx
    rw [hx]
    exact hLap x
  have hcont := (scalarHeatFamily_continuousOn_nonneg g μ hμ
    (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k)))
  have hInt : IntervalIntegrable (fun s => scalarHeatFamily g μ hμ s
      (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k))) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le
    (hcont.mono (show Set.Icc (0 : ℝ) T ⊆ Set.Ici 0 from Set.Icc_subset_Ici_self))
  have hbound := lp_interval_integral_uniform_bound μ hT hK0 hInt
    (fun t ht => scalarHeatFamily_linf g μ hμ ht.1.le K hK0 _ hL)
  rw [scalarHeat_compact_duhamel g hK μ hμ k hT] at hbound
  filter_upwards [hbound, Lp.coeFn_sub (scalarHeatFamily g μ hμ T (scalarEnergyDomainL2 g μ hμ k))
    (scalarEnergyDomainL2 g μ hμ k), scalarEnergyDomainL2_coe g μ hμ k] with x hx hs hk
  simpa only [hs, Pi.sub_apply, hk] using hx

end Yau.LeafProofs.L19Aux
