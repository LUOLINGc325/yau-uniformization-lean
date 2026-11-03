import Yau.Proofs.F04OpenTimeMass

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The actual evolving density mass has its true derivative with only
 closed C0 and positive-time C1 for z, matching the original F05 output. -/
theorem flow_cutoff_mass_derivative_openTime
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) {z χ : STF X}
    (hzC : ContinuousOn (fun p : Pt X × ℝ => z p.1 p.2) (univ ×ˢ Icc 0 T))
    (hz : SmoothSpaceC1Time z (Ioo 0 T)) (hχ : SmoothSpaceC1Time χ (Icc 0 T))
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun t => ∫ x, massCutoff u R x*(z x t*χ x t*density ρ x t) ∂μ) (Icc 0 T) ∧
      ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ∫ x, massCutoff u R x*(z x s*χ x s*density ρ x s) ∂μ)
          (∫ x, massCutoff u R x*
            ((deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
              scalarCurvature (h t) x*(z x t*χ x t*density ρ x t)) ∂μ) t := by
  have hden : SmoothSpaceTime (density ρ) (Icc 0 T) := (massVolumeTransport o h U P ρ hloc T hT).1
  have hdc := smoothSpaceTime_c1 hden
  have hχI := smoothSpaceC1Time_mono hχ (show Ioo 0 T ⊆ Icc 0 T from Ioo_subset_Icc_self)
  have hdI := smoothSpaceC1Time_mono hdc (show Ioo 0 T ⊆ Icc 0 T from Ioo_subset_Icc_self)
  have hProd := smoothSpaceC1Time_mul (smoothSpaceC1Time_mul hz hχI) hdI
  have hProdC := (hzC.mul (smoothSpaceC1Time_continuousOn hχ)).mul (smoothSpaceTime_continuousOn hden)
  have hh := cutoff_mass_differentiation_openTime X.metric μ hμ hProdC hProd (massCutoff_smooth hu.1 R)
    (massCutoff_compact X o u hu hR)
  refine ⟨hh.1,?_⟩
  intro t ht
  have he (x : Pt X) : deriv (fun s => z x s*χ x s*density ρ x s) t =
      (deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
        scalarCurvature (h t) x*(z x t*χ x t*density ρ x t) := by
    have hzD := smoothSpaceC1Time_hasDerivAt isOpen_Ioo hz x ht
    have hχD := smoothSpaceC1Time_hasDerivAt isOpen_Ioo hχI x ht
    have hdD := (density_hasDerivWithinAt o h U P ρ hloc x t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
    have hd := ((hzD.mul hχD).mul hdD).deriv
    change deriv (z x*χ x*density ρ x) t = _
    rw [hd]
    simp only [Pi.mul_apply]
    ring
  have hInt : (∫ x, massCutoff u R x*deriv (fun s => z x s*χ x s*density ρ x s) t ∂μ) =
      ∫ x, massCutoff u R x*
        ((deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
          scalarCurvature (h t) x*(z x t*χ x t*density ρ x t)) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => congrArg (fun a => massCutoff u R x*a) (he x))
  rw [← hInt]
  exact hh.2 t ht

end Yau.F04Proof
