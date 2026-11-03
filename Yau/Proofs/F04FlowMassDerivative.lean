import Yau.Proofs.F04CutoffMass
import Yau.Proofs.F04MassCutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem smoothSpaceTime_c1 {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I) : SmoothSpaceC1Time v I := by
  refine ⟨?_, fun x => (hv x).of_le (by norm_num)⟩
  intro t ht x
  exact (hv x).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, ht⟩)

theorem smoothSpaceC1Time_mono {n : ℕ} {M : ComplexManifold n} {I J : Set ℝ}
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I) (hJI : J ⊆ I) :
    SmoothSpaceC1Time v J :=
  ⟨fun t ht => hv.1 t (hJI ht), fun x => (hv.2 x).mono (Set.prod_mono (Subset.refl _) hJI)⟩

/-- Every mass below has one genuine compact spatial cutoff. The derivative
is computed against the fixed initial measure, including its true density term. -/
theorem flow_cutoff_mass_derivative {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) {z χ : STF X}
    (hz : SmoothSpaceTime z (Icc 0 T)) (hχ : SmoothSpaceC1Time χ (Icc 0 T))
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun t => ∫ x, massCutoff u R x * (z x t * χ x t * density ρ x t) ∂μ) (Icc 0 T) ∧
      ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ∫ x, massCutoff u R x * (z x s * χ x s * density ρ x s) ∂μ)
          (∫ x, massCutoff u R x *
            ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
              scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ∂μ) t := by
  have hden : SmoothSpaceTime (density ρ) (Icc 0 T) := (massVolumeTransport o h U P ρ hloc T hT).1
  have hzc := smoothSpaceTime_c1 hz
  have hdc := smoothSpaceTime_c1 hden
  have hv := smoothSpaceC1Time_mul (smoothSpaceC1Time_mul hzc hχ) hdc
  have hh := cutoff_mass_differentiation X.metric μ hμ hv (massCutoff_smooth hu.1 R)
    (massCutoff_compact X o u hu hR)
  refine ⟨hh.1, ?_⟩
  intro t ht
  have hzI := smoothSpaceC1Time_mono hzc (show Ioo 0 T ⊆ Icc 0 T from Ioo_subset_Icc_self)
  have hχI := smoothSpaceC1Time_mono hχ (show Ioo 0 T ⊆ Icc 0 T from Ioo_subset_Icc_self)
  have he (x : Pt X) : deriv (fun s => z x s * χ x s * density ρ x s) t =
      (deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
        scalarCurvature (h t) x * (z x t * χ x t * density ρ x t) := by
    have hzD := smoothSpaceC1Time_hasDerivAt isOpen_Ioo hzI x ht
    have hχD := smoothSpaceC1Time_hasDerivAt isOpen_Ioo hχI x ht
    have hdD := (density_hasDerivWithinAt o h U P ρ hloc x t ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)
    have hd := ((hzD.mul hχD).mul hdD).deriv
    change deriv (z x * χ x * density ρ x) t = _
    rw [hd]
    simp only [Pi.mul_apply]
    ring
  have hInt : (∫ x, massCutoff u R x * deriv (fun s => z x s * χ x s * density ρ x s) t ∂μ) =
      ∫ x, massCutoff u R x *
        ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
          scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => congrArg (fun a => massCutoff u R x * a) (he x))
  rw [← hInt]
  exact hh.2 t ht

end Yau.F04Proof
