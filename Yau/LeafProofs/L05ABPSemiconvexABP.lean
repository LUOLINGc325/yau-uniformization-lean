import Yau.LeafProofs.L05ABPSemiconvexBounds
import Yau.LeafProofs.L05ABPContactLimit
import Yau.LeafProofs.L05ABPViscosityApprox

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance L05ABPSemiconvexABP_pointVolumeHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem spatialD_sub_const {n : ℕ} (u : Point n → ℝ) (c : ℝ) (z : Point n) :
    spatialD (fun q => u q-c) z=spatialD u z := by
  exact fderiv_sub_const _

theorem spatialGrad_sub_const {n : ℕ} (u : Point n → ℝ) (c : ℝ) (z : Point n) :
    spatialGrad (fun q => u q-c) z=spatialGrad u z := by
  simp only [spatialGrad,spatialD_sub_const]

theorem timeD_sub_const {n : ℕ} (u : Point n → ℝ) (c : ℝ) (z : Point n) :
    timeD Set.univ (fun q => u q-c) z=timeD Set.univ u z := by
  simpa only [add_zero,sub_eq_add_neg] using timeD_translate u (0 : Point n) (-c) z

theorem hessian_sub_const {n : ℕ} (u : Point n → ℝ) (c : ℝ) (z : Point n) :
    hessian (fun q => u q-c) z=hessian u z := by
  simpa only [add_zero,sub_eq_add_neg] using hessian_translate u (0 : Point n) (-c) z

theorem pastSupports_sub_const {n : ℕ} {R a : ℝ} (u : Point n → ℝ) (c : ℝ)
    (z : Point n) (xi : Space n) :
    pastSupports R a (fun q => u q-c) z xi ↔ pastSupports R a u z xi := by
  constructor
  · intro h y hy s hs
    have hh := h y hy s hs
    change u (y,s)-c≤u z-c+inner ℝ xi (y-z.1) at hh
    linarith
  · intro h y hy s hs
    have hh := h y hy s hs
    change u (y,s)-c≤u z-c+inner ℝ xi (y-z.1)
    linarith

theorem smoothContact_sub_const {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) (c : ℝ) :
    smoothContact R a b (fun q => u q-c)=smoothContact R a b u := by
  ext z
  change (z ∈ abpOpen n R a b ∧ pastSupports R a (fun q => u q-c) z
    (spatialGrad (fun q => u q-c) z)) ↔ _
  rw [spatialGrad_sub_const,pastSupports_sub_const]
  rfl

theorem contactMap_sub_const {n : ℕ} (u : Point n → ℝ) (c : ℝ) :
    contactMap (fun q => u q-c)=fun q => contactMap u q-(0,c) := by
  funext q
  apply Prod.ext
  · simp only [contactMap,spatialGrad_sub_const,Prod.fst_sub,sub_zero]
  · simp only [contactMap,spatialGrad_sub_const,Prod.snd_sub]
    ring

theorem smoothContactDensity_sub_const {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) (c : ℝ) :
    smoothContactDensity R a b (fun q => u q-c)=smoothContactDensity R a b u := by
  unfold smoothContactDensity
  rw [smoothContact_sub_const]
  congr 1
  funext z
  rw [contactMap_sub_const,fderiv_sub_const]

/-- The geometric ABP theorem for bounded semiconvex functions. The sole PDE
premise is a literal a.e. inequality on Peano jets at past support points. -/
theorem semiconvex_contact_abp_power {n : ℕ} {R a b k K B : ℝ} {w g : Point n → ℝ}
    (hR : 0<R) (hR1 : R≤1) (hab : a<b) (hk : 0<k)
    (hu : Continuous w) (hw : jointSemiconvex K w) (hK : 0≤K) (hB : 0≤B)
    (hb : ∀ z, |w z|≤B) (hg : ContinuousOn g (abpClosed n R a b))
    (hboundary : ∀ z ∈ abpBoundary n R a b, w z≤0)
    (hsource : ∀ᵐ z ∂(volume.restrict (abpOpen n R a b)),
      ∀ (l : Point n →L[ℝ] ℝ) (B0 : Point n →L[ℝ] Point n →L[ℝ] ℝ),
        jointPeanoJet w z l B0 → pastSupports R a w z (spatialGrad w z) →
          l (0,1)+k*Matrix.trace (-(jointHessian B0 : Mat n))≤g z)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) :
    abpKappa n*(max (w z0) 0)^(2*n+1)≤
      (k⁻¹)^(2*n)*∫ z in abpOpen n R a b, (max (g z) 0)^(2*n+1) := by
  let C : NNReal := ⟨2*B+K,by positivity⟩
  have hLip : LipschitzWith C w := bounded_jointSemiconvex_lipschitz hw hK hB hb
  let r : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hr (j : ℕ) : 0<r j := by dsimp only [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrT : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0,Filter.Eventually.of_forall hr⟩
  let U : ℕ → Point n → ℝ := fun j z => abpMollify (r j) w z-(C:ℝ)*r j
  have hUsmooth (j : ℕ) : ContDiff ℝ ∞ (U j) := (abpMollify_smooth (hr j) hu).sub contDiff_const
  have hUboundary (j : ℕ) (z : Point n) (hz : z ∈ abpBoundary n R a b) : U j z≤0 := by
    have he := (abs_le.mp (abpMollify_lipschitz_approx (hr j) hLip z)).2
    have hwz := hboundary z hz
    dsimp only [U]
    linarith
  have hUvalues (q : Point n) (_hq : q ∈ abpClosed n R a b) :
      Tendsto (fun j => U j q) atTop (𝓝 (w q)) := by
    have hm := (abpMollify_lipschitz_tendsto hLip q).comp hrT
    have he : Tendsto (fun j => (C:ℝ)*r j) atTop (𝓝 0) := by simpa using hr0.const_mul (C:ℝ)
    simpa only [U,Function.comp_def,sub_zero] using hm.sub he
  let M := semiconvexDensityBound n B K
  have hMnon : 0≤M := semiconvexDensityBound_nonneg n hB hK
  have hbound (j : ℕ) : smoothContactDensity R a b (U j)≤ᵐ[volume.restrict (abpOpen n R a b)]
      (fun _ => M) := by
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [U]
    rw [smoothContactDensity_sub_const]
    exact abpMollify_boundedSemiconvex_density_bound (hr j) hu hw hK hB hb R a b z
  let F : Point n → ℝ := fun z => (k⁻¹)^(2*n)*(max (g z) 0)^(2*n+1)
  have hQmeas : MeasurableSet (abpOpen n R a b) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet
  have hlim : ∀ᵐ z ∂(volume.restrict (abpOpen n R a b)),
      limsup (fun j => ENNReal.ofReal (smoothContactDensity R a b (U j) z)) atTop≤ENNReal.ofReal (F z) := by
    filter_upwards [ae_restrict_of_ae (jointSemiconvex_ae_peano hw),hsource,ae_restrict_mem hQmeas]
      with z hpeano hsrc hz
    obtain ⟨l,B0,hP⟩ := hpeano
    have hgrad : Tendsto (fun j => spatialGrad (U j) z) atTop (𝓝 (spatialGrad w z)) := by
      simp only [U,spatialGrad_sub_const]
      exact (jointPeanoJet_mollifier_spatialGrad_tendsto hu hP).comp hrT
    have ht : Tendsto (fun j => timeD Set.univ (U j) z) atTop (𝓝 (l (0,1))) := by
      simp only [U,timeD_sub_const]
      exact (jointPeanoJet_mollifier_timeD_tendsto hu hP).comp hrT
    have hH : Tendsto (fun j => hessian (U j) z) atTop (𝓝 (jointHessian B0)) := by
      simp only [U,hessian_sub_const]
      exact (jointPeanoJet_mollifier_hessian_tendsto hu hP).comp hrT
    exact smoothContactDensity_limsup_bound hk hz hUsmooth hUvalues hgrad ht hH (hsrc l B0 hP)
  have hD : IsCompact (abpClosed n R a b) := (isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
  have hQsub : abpOpen n R a b ⊆ abpClosed n R a b :=
    fun z hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  have hMint : IntegrableOn (fun _ : Point n => M) (abpOpen n R a b) :=
    ((continuous_const : Continuous (fun _ : Point n => M)).continuousOn.integrableOn_compact hD).mono_set hQsub
  have hFc : ContinuousOn F (abpClosed n R a b) := by
    intro z hz
    exact (((hg z hz).sup continuousWithinAt_const).pow (2*n+1)).const_mul _
  have hFint : IntegrableOn F (abpOpen n R a b) := (hFc.integrableOn_compact hD).mono_set hQsub
  have hFn : 0≤ᵐ[volume.restrict (abpOpen n R a b)] F :=
    Filter.Eventually.of_forall fun z => mul_nonneg (pow_nonneg (inv_nonneg.mpr hk.le) _)
      (pow_nonneg (le_max_right _ _) _)
  have hi := smooth_contact_density_limit hR hR1 hab hUsmooth hUboundary hMint
    (Filter.Eventually.of_forall fun _ => hMnon) hbound hFint hFn hlim hz0 (hUvalues z0 hz0)
  change abpKappa n*(max (w z0) 0)^(2*n+1)≤
    ∫ z in abpOpen n R a b, (k⁻¹)^(2*n)*(max (g z) 0)^(2*n+1) at hi
  rwa [integral_const_mul] at hi

end Yau.LeafProofs.L05Aux
