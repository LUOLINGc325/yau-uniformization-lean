import Yau.Proofs.F03KernelPotentialFubini
import Yau.Proofs.F03KernelSlabContinuity

/-! The actual unbounded potential heat has its genuine physical-time derivative on both closed slab faces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_U_hasDerivWithinAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (x : Pt X) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y r ∂μ)
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*P y s ∂μ)
      (Icc 0 T) s := by
  let k := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x
  let q : ℝ → ℝ := fun r => ∫ y,k y*P y r ∂μ
  have hJoint := dirichletMinimalKernel_P_slab_continuous X o h U P ρ hf hT μ hμ O hO hb
  have hFix : Continuous (fun r : Icc (0:ℝ) T => q r.val) :=
    hJoint.comp (continuous_const.prodMk continuous_id)
  have hCont : ContinuousOn q (Icc 0 T) := continuousOn_iff_continuous_restrict.mpr hFix
  have hInt : IntervalIntegrable q volume 0 s :=
    (hCont.mono (show Icc (0:ℝ) s ⊆ Icc 0 T from fun r hr => ⟨hr.1,hr.2.trans hs.2⟩)).intervalIntegrable_of_Icc hs.1
  letI : Fact (s ∈ Icc (0:ℝ) T) := ⟨hs⟩
  have hD : HasDerivWithinAt (fun r => ∫ t in (0:ℝ)..r,q t) (q s) (Icc 0 T) s :=
    intervalIntegral.integral_hasDerivWithinAt_right hInt
      (hCont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hCont s hs)
  exact hD.congr_of_mem
    (fun r hr => dirichletMinimalKernel_U_eq_integral_P X o h U P ρ hf hT μ hμ O hO hb x hr) hs

theorem dirichletMinimalKernel_U_hasDerivAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (x : Pt X) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y r ∂μ)
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*P y s ∂μ) s := by
  have hS : 0 ≤ s+1 := by linarith
  have hMem : s ∈ Icc (0:ℝ) (s+1) := ⟨hs.le,by linarith⟩
  exact (dirichletMinimalKernel_U_hasDerivWithinAt X o h U P ρ hf hS μ hμ O hO hb x hMem).hasDerivAt
    (Icc_mem_nhds hs (by linarith))

theorem dirichletMinimalKernel_centered_eq
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (x : Pt X) {s : ℝ} (hs : s ∈ Icc 0 T) :
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*
      centeredFlowPotential X U T y s ∂μ)=
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y s ∂μ)-
        (s/T)*(∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y T ∂μ) := by
  have hIntS := (dirichletMinimalKernel_potential_slab_integrable X o h U P ρ hf hT μ hμ O hO hb x hs).2
  have hIntT := (dirichletMinimalKernel_potential_slab_integrable X o h U P ρ hf hT μ hμ O hO hb x ⟨hT,le_rfl⟩).2
  calc
    _ = ∫ y,(dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y s)-
        (s/T)*(dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y T) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ (fun y => by dsimp [centeredFlowPotential];ring)
    _ = _ := by rw [integral_sub hIntS (hIntT.const_mul (s/T)),integral_const_mul]

theorem dirichletMinimalKernel_centered_hasDerivWithinAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (x : Pt X) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*
        centeredFlowPotential X U T y r ∂μ)
      ((∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*P y s ∂μ)-
        (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y T ∂μ)/T)
      (Icc 0 T) s := by
  have hU := dirichletMinimalKernel_U_hasDerivWithinAt X o h U P ρ hf hT μ hμ O hO hb x hs
  have hLinear := (((hasDerivAt_id s).div_const T).mul_const
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y T ∂μ)).hasDerivWithinAt
      (s := Icc 0 T)
  have hDifference := (hU.sub hLinear).congr_of_mem
    (fun r hr => dirichletMinimalKernel_centered_eq X o h U P ρ hf hT μ hμ O hO hb x hr) hs
  convert hDifference using 1 <;> ring

end Yau.Proofs.F03Aux
