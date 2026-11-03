import Yau.LeafProofs.L17ResidualScaling
import Yau.LeafProofs.L17LocalizedSchauderTransport

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem parabolicScalePoint_mem_two_ball_cylinder {ρ T : ℝ} (hρ : 0 < ρ)
    {q : Point n} (hq : q ∈ cylinder (ball (0 : Space n) (2*ρ)) 0 T) :
    parabolicScalePoint ρ q ∈ cylinder (ball (0 : Space n) 2) 0 (T/ρ^2) := by
  refine ⟨?_,parabolic_timeScale_mem_Icc hρ.ne' hq.2⟩
  have hx : ‖q.1‖ < 2*ρ := by simpa only [mem_ball,dist_zero_right] using hq.1
  change ρ⁻¹ • q.1 ∈ ball (0 : Space n) 2
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ),← div_eq_inv_mul]
  exact (div_lt_iff₀ hρ).mpr hx

theorem localGaussianResidual_physical_profile (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ C : ℝ} (hγ : 0 < γ) (f : HolderSpace P T γ) (p : P.centers)
    (hR : HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
      (unitGaussianResidual P T hT f p) C) :
    ContinuousOn (localGaussianResidual P T hT f p) (cylinder (ball 0 (2*P.radius)) 0 T) ∧
    (∀ q ∈ cylinder (ball (0 : Space n) (2*P.radius)) 0 T, |localGaussianResidual P T hT f p q| ≤ C) ∧
    ∀ q ∈ cylinder (ball (0 : Space n) (2*P.radius)) 0 T,
      ∀ r ∈ cylinder (ball (0 : Space n) (2*P.radius)) 0 T,
        |localGaussianResidual P T hT f p q-localGaussianResidual P T hT f p r| ≤
          2*C*(parabolicDistance q r/P.radius)^γ := by
  have hMap : MapsTo (parabolicScalePoint P.radius) (cylinder (ball (0 : Space n) (2*P.radius)) 0 T)
      (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2)) :=
    fun _ hq => parabolicScalePoint_mem_two_ball_cylinder P.radius_pos hq
  refine ⟨?_,?_,?_⟩
  · apply ((L16Aux.holderBound_continuousOn hγ hR).comp
      (parabolicScalePoint_continuous P.radius).continuousOn hMap).congr
    intro q _
    exact localGaussianResidual_eq_unit P T hT f p q
  · intro q hq
    rw [localGaussianResidual_eq_unit]
    simpa only [Real.norm_eq_abs] using hR.2.1 _ (hMap hq)
  · intro q hq r hr
    rw [localGaussianResidual_eq_unit,localGaussianResidual_eq_unit]
    calc
      _ ≤ C*holderWeight γ (parabolicScalePoint P.radius q) (parabolicScalePoint P.radius r) := by
        simpa only [Real.norm_eq_abs] using hR.2.2 _ (hMap hq) _ (hMap hr)
      _ ≤ C*(2*parabolicDistance (parabolicScalePoint P.radius q) (parabolicScalePoint P.radius r)^γ) :=
        mul_le_mul_of_nonneg_left (holderWeight_le_two_parabolicDistance_rpow hγ.le _ _) hR.1
      _ = _ := by rw [parabolicDistance_scalePoint P.radius_pos]; ring

theorem localGaussianResidual_zero_outside (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (hRadius : 2*P.radius < P.charts.radius) {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers)
    {z : Space n} (hz : z ∈ ball (0 : Space n) (2*P.radius))
    (hn : z ∉ closedBall (0 : Space n) P.radius) (τ : ℝ) :
    localGaussianResidual P T hT f p (z,τ) = 0 := by
  let e := P.charts.chart p
  have hzSource : z ∈ e.source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball hRadius.le) hz))
  have hNotCover : e z ∉ e '' closedBall (0 : Space n) P.radius := by
    rintro ⟨w,hw,hwz⟩
    have heq : w=z := e.injOn (chart_closedBall_source P p hw) hzSource hwz
    exact hn (heq ▸ hw)
  have he : ContinuousAt e z := e.continuousOn.continuousAt (e.open_source.mem_nhds hzSource)
  have hzero : (fun w => P.localization p (e w)) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [he.eventually ((cutoff_cover_isCompact P p).isClosed.isOpen_compl.mem_nhds hNotCover)] with w hw
    exact localization_zero_of_not_cover P p hw
  have h0 : P.localization p (e z) = 0 := hzero.eq_of_nhds
  have h1 : fderiv ℝ (fun w => P.localization p (e w)) z = 0 := by
    simpa using (hzero.fderiv_eq (𝕜 := ℝ))
  have h2 : fderiv ℝ (fderiv ℝ (fun w => P.localization p (e w))) z = 0 := by
    simpa using ((hzero.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))
  dsimp only [e] at h0 h1 h2
  simp only [localGaussianResidual,realHessianContraction,gradientCrossContraction,h0,h1,h2,
    zero_apply,zero_mul,mul_zero,add_zero,Finset.sum_const_zero,sub_zero]

def physicalGaussianResidual (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Space n × Time T) : ℝ :=
  if q.1 ∈ ball (0 : Space n) (2*P.radius) then localGaussianResidual P T hT f p (q.1,(q.2 : ℝ)) else 0

theorem physicalGaussianResidual_zero_outside (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (hRadius : 2*P.radius < P.charts.radius) {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers)
    (z : Space n) (hz : z ∉ closedBall (0 : Space n) P.radius) (t : Time T) :
    physicalGaussianResidual P T hT f p (z,t) = 0 := by
  by_cases hB : z ∈ ball (0 : Space n) (2*P.radius)
  · rw [physicalGaussianResidual,ite_eq_left hB]
    exact localGaussianResidual_zero_outside P T hT hRadius f p hB hz _
  · rw [physicalGaussianResidual,ite_eq_right hB]

theorem physicalGaussianResidual_profile (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ C : ℝ} (hγ : 0 < γ) (f : HolderSpace P T γ) (p : P.centers)
    (hR : HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
      (unitGaussianResidual P T hT f p) C) :
    let Q := ball (0 : Space n) (2*P.radius) ×ˢ (Set.univ : Set (Time T))
    ContinuousOn (physicalGaussianResidual P T hT f p) Q ∧
    (∀ q ∈ Q, |physicalGaussianResidual P T hT f p q| ≤ C) ∧
    ∀ q ∈ Q, ∀ r ∈ Q,
      |physicalGaussianResidual P T hT f p q-physicalGaussianResidual P T hT f p r| ≤
        2*C*(parabolicDistance (q.1,(q.2 : ℝ)) (r.1,(r.2 : ℝ))/P.radius)^γ := by
  obtain ⟨hc,hSup,hDiff⟩ := localGaussianResidual_physical_profile P T hT hγ f p hR
  have hMap : Continuous (fun q : Space n × Time T => (q.1,(q.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hMem : ∀ q : Space n × Time T, q.1 ∈ ball (0 : Space n) (2*P.radius) →
      (q.1,(q.2 : ℝ)) ∈ cylinder (ball (0 : Space n) (2*P.radius)) 0 T :=
    fun q hq => ⟨hq,q.2.property⟩
  refine ⟨?_,?_,?_⟩
  · apply (hc.comp hMap.continuousOn (fun q hq => hMem q hq.1)).congr
    intro q hq
    exact ite_eq_left hq.1
  · intro q hq
    rw [physicalGaussianResidual,ite_eq_left hq.1]
    exact hSup _ (hMem q hq.1)
  · intro q hq r hr
    rw [physicalGaussianResidual,ite_eq_left hq.1,physicalGaussianResidual,ite_eq_left hr.1]
    exact hDiff _ (hMem q hq.1) _ (hMem r hr.1)

end Yau.LeafProofs.L17Aux
