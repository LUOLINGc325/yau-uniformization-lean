import Yau.Proofs.F03KernelFarInitialLimit
import Yau.Proofs.F03TerminalProfileIntegrable

/-! Compact localization and the genuine Gaussian far-source estimate give the initial value of an unbounded continuous profile. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_terminal_profile_initial_limit
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (f : Pt X → ℝ) (hfCont : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hBound : ∀ y,|f y| ≤ A*(1+ρ y T)) (x : Pt X) :
    Tendsto (fun b => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y ∂μ)
      (𝓝[>] 0) (𝓝 (f x)) := by
  obtain ⟨η,hη,hcη,hRange,hηOne,_hsη⟩ := exists_smooth_compact_cutoff X.metric x
    (r := 1) (R := 2) zero_lt_one (by norm_num)
  have hηx : η x=1 := hηOne x (by rw [X.metric.induced_distance_eq_zero.mpr rfl];norm_num)
  have hηCont := continuous_of_smoothFn hη
  have hCompact := dirichletMinimalKernelCandidate_compact_initial X.metric X.kahler_metric μ hμ O hO
    (fun y => η y*f y) (hηCont.mul hfCont) hcη.mul_right x
  have hCompactRight : Tendsto (fun b => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*(η y*f y) ∂μ)
      (𝓝[>] 0) (𝓝 (f x)) := by
    rw [hηx,one_mul] at hCompact
    apply hCompact.congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    apply integral_congr_ae
    exact ae_of_all μ (fun y => by
      change dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b y x*(η y*f y)=_
      rw [dirichletMinimalKernelCandidate_symm X.metric X.kahler_metric μ hμ O hO hb y x])
  have hCompactBound (y : Pt X) : |η y*f y| ≤ A*(1+ρ y T) := by
    rw [abs_mul,abs_of_nonneg (hRange y).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hRange y).2).trans (hBound y)
  have hFarBound (y : Pt X) : |(1-η y)*f y| ≤ A*(1+ρ y T) := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hRange y).2)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hRange y).1])).trans (hBound y)
  have hFar := dirichletMinimalKernel_far_source_initial_limit X o h U P ρ hf hT μ hμ O hO x
    (fun y => (1-η y)*f y) hA hFarBound
    (fun y hy => by rw [hηOne y hy,sub_self,zero_mul])
  have hSum := hCompactRight.add hFar
  simp only [add_zero] at hSum
  apply hSum.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hIntC := dirichletMinimalKernel_terminal_profile_integrable X o h U P ρ hf hT μ hμ O hO
    (fun y => η y*f y) (hηCont.mul hfCont).aestronglyMeasurable hA hCompactBound hb x
  have hIntF := dirichletMinimalKernel_terminal_profile_integrable X o h U P ρ hf hT μ hμ O hO
    (fun y => (1-η y)*f y) ((continuous_const.sub hηCont).mul hfCont).aestronglyMeasurable hA hFarBound hb x
  change (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*(η y*f y) ∂μ)+
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*((1-η y)*f y) ∂μ)=_
  rw [← integral_add hIntC hIntF]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*(η y*f y)+
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*((1-η y)*f y)=_
    ring)

end Yau.Proofs.F03Aux
