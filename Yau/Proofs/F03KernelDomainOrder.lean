import Yau.Proofs.F03FinitePointwiseDomination
import Yau.Proofs.F03KernelRowAmbient
import Yau.Proofs.F03DirichletKernelProducer

/-! The ONE actual Dirichlet kernel increases with its actual open domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletEvaluationVector_ambient_mono_domain (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω Γ : Set M.Carrier) (hΩ : IsOpen Ω) (hΓ : IsOpen Γ) (hΩΓ : Ω ⊆ Γ)
    (t : ℝ) (ht : 0 < t) (x : M.Carrier) (hx : x ∈ Ω) :
    ∀ᵐ y ∂μ,
      l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) y ≤
        l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Γ hΓ x (hΩΓ hx) t ht) y := by
  let a := l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht)
  let b := l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Γ hΓ x (hΩΓ hx) t ht)
  have hd : ∀ᵐ y ∂μ, 0 ≤ (b-a) y := by
    apply lp_nonneg_of_inner_nonneg
    intro f hf
    rw [inner_sub_left]
    change 0 ≤ inner ℝ
      (l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Γ hΓ x (hΩΓ hx) t ht)) f-
      inner ℝ (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht)) f
    rw [l2ZeroExtension_inner_left,l2ZeroExtension_inner_left,
      dirichletHeatEvaluationVector_inner,dirichletHeatEvaluationVector_inner]
    exact sub_nonneg.mpr (dirichletClassicalHeat_mono_domain g hK μ hμ Ω Γ hΩ hΓ hΩΓ t ht f
      ((Lp.coeFn_nonneg _).mp hf) x hx)
  filter_upwards [hd,Lp.coeFn_sub b a] with y hy hs
  rw [hs,Pi.sub_apply] at hy
  exact sub_nonneg.mp hy

theorem dirichletKernelCandidate_mono_domain (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω Γ : Set M.Carrier) (hΩ : IsOpen Ω) (hΓ : IsOpen Γ) (hΩΓ : Ω ⊆ Γ)
    {t : ℝ} (ht : 0 < t) (x y : M.Carrier) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x y ≤ dirichletKernelCandidate g hK μ hμ Γ hΓ t x y := by
  by_cases hx : x ∈ Ω
  · by_cases hy : y ∈ Ω
    · have hAE : ∀ᵐ z ∂μ, dirichletKernelCandidate g hK μ hμ Ω hΩ t x z ≤
          dirichletKernelCandidate g hK μ hμ Γ hΓ t x z := by
        filter_upwards [dirichletEvaluationVector_ambient_mono_domain g hK μ hμ Ω Γ hΩ hΓ hΩΓ t ht x hx,
          dirichletKernelCandidate_row_ambient_ae g hK μ hμ Ω hΩ ht x hx,
          dirichletKernelCandidate_row_ambient_ae g hK μ hμ Γ hΓ ht x (hΩΓ hx)] with z hz hΩz hΓz
        exact hΩz.trans_le (hz.trans_eq hΓz.symm)
      have hΩc : ContinuousOn (dirichletKernelCandidate g hK μ hμ Ω hΩ t x) Ω := by
        rw [dirichletKernelCandidate_row_classical g hK μ hμ Ω hΩ ht x hx]
        exact dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ _ (half_pos ht)
      have hΓc : ContinuousOn (dirichletKernelCandidate g hK μ hμ Γ hΓ t x) Γ := by
        rw [dirichletKernelCandidate_row_classical g hK μ hμ Γ hΓ ht x (hΩΓ hx)]
        exact dirichletClassicalHeat_continuousOn g hK μ hμ Γ hΓ _ (half_pos ht)
      exact leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ _ _ hΩc (hΓc.mono hΩΓ)
        (ae_restrict_of_ae hAE) y hy
    · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inr hy)]
      exact dirichletKernelCandidate_nonneg g hK μ hμ Γ hΓ ht x y
  · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inl hx)]
    exact dirichletKernelCandidate_nonneg g hK μ hμ Γ hΓ ht x y

end Yau.Proofs.F03Aux
