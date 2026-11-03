import Yau.Proofs.P06HodgeRegularityJetClosedGraph

/-! A finite distributional jet with a continuous compact representative
is a bounded linear map on a Banach domain. This does not require an
infinite-order smooth representative of every element of that domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BoundedContinuousFunction InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem compactBCF_eq_of_test_pairings {K : Set E} (hK : IsCompact K)
    (f g : E →ᵇ ℝ) (hf : tsupport (f : E → ℝ) ⊆ K)
    (hg : tsupport (g : E → ℝ) ⊆ K)
    (hp : ∀ φ, regularityTest Set.univ φ →
      (∫ z, f z * φ z ∂ν) = ∫ z, g z * φ z ∂ν) : f = g := by
  have hfc : HasCompactSupport (f : E → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hf
  have hgc : HasCompactSupport (g : E → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hg
  have he : (f : E → ℝ) =ᵐ[ν] (g : E → ℝ) := by
    have hh := regularity_ae_eq_of_test_integrals ν isOpen_univ
      ((f.continuous.memLp_of_hasCompactSupport hfc).restrict Set.univ)
      ((g.continuous.memLp_of_hasCompactSupport hgc).restrict Set.univ)
      (fun φ hφ => by simpa only [Measure.restrict_univ] using hp φ hφ)
    simpa only [Measure.restrict_univ] using hh
  apply BoundedContinuousFunction.ext
  intro z
  exact congrFun (Measure.eq_of_ae_eq he f.continuous g.continuous) z

def distributionLiftLinear (P : H →L[ℝ] Lp ℝ 2 ν)
    (D : ∀ φ : E → ℝ, regularityTest Set.univ φ → Lp ℝ 2 ν)
    (R : H → (E →ᵇ ℝ)) {K : Set E} (hK : IsCompact K)
    (hRK : ∀ f, tsupport (R f : E → ℝ) ⊆ K)
    (hpair : ∀ f φ hφ, (∫ z, R f z * φ z ∂ν) = inner ℝ (P f) (D φ hφ)) :
    H →ₗ[ℝ] (E →ᵇ ℝ) where
  toFun := R
  map_add' f g := by
    apply compactBCF_eq_of_test_pairings ν hK (R (f+g)) (R f+R g) (hRK _)
      ((tsupport_add _ _).trans (Set.union_subset (hRK _) (hRK _)))
    intro φ hφ
    change (∫ z, R (f+g) z * φ z ∂ν) = ∫ z, (R f z+R g z)*φ z ∂ν
    have hφI := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1 (μ := ν)
    simp only [add_mul]
    rw [integral_add (regularityBCF_mul_integrable ν φ hφI (R f))
      (regularityBCF_mul_integrable ν φ hφI (R g)),hpair (f+g) φ hφ,
      hpair f φ hφ,hpair g φ hφ,map_add,inner_add_left]
  map_smul' a f := by
    apply compactBCF_eq_of_test_pairings ν hK (R (a • f)) (a • R f) (hRK _)
      ((tsupport_smul_subset_right (fun _ => a) (R f : E → ℝ)).trans (hRK f))
    intro φ hφ
    change (∫ z, R (a • f) z * φ z ∂ν) = ∫ z, (a * R f z)*φ z ∂ν
    simp_rw [mul_assoc]
    rw [integral_const_mul,hpair (a • f) φ hφ,hpair f φ hφ,map_smul,real_inner_smul_left]

theorem distributionLiftLinear_continuous (P : H →L[ℝ] Lp ℝ 2 ν)
    (D : ∀ φ : E → ℝ, regularityTest Set.univ φ → Lp ℝ 2 ν)
    (R : H → (E →ᵇ ℝ)) {K : Set E} (hK : IsCompact K)
    (hRK : ∀ f, tsupport (R f : E → ℝ) ⊆ K)
    (hpair : ∀ f φ hφ, (∫ z, R f z * φ z ∂ν) = inner ℝ (P f) (D φ hφ)) :
    Continuous (distributionLiftLinear ν P D R hK hRK hpair) := by
  let L := distributionLiftLinear ν P D R hK hRK hpair
  apply L.continuous_of_seq_closed_graph
  intro us f y hus hy
  have hy0 (z : E) (hz : z ∉ K) : y z = 0 := by
    have heval := ((BoundedContinuousFunction.lipschitz_eval_const z).continuous.tendsto y).comp hy
    have hzero (m : ℕ) : L (us m) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hRK (us m) h))
    have ht : Tendsto (fun m => L (us m) z) atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique heval ht
  have hyK : tsupport (y : E → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    exact hz (hy0 z hzK)
  have he : y = R f := by
    apply compactBCF_eq_of_test_pairings ν hK y (R f) hyK (hRK f)
    intro φ hφ
    have hφI := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1 (μ := ν)
    have htarget := ((regularityBCFPairing ν φ hφI).continuous.tendsto y).comp hy
    have hsource : Tendsto (fun m => inner ℝ (P (us m)) (D φ hφ)) atTop
        (𝓝 (inner ℝ (P f) (D φ hφ))) := ((P.continuous.tendsto f).comp hus).inner
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => D φ hφ) atTop (𝓝 (D φ hφ)))
    have hsource' : Tendsto (fun m => ∫ z, L (us m) z * φ z ∂ν) atTop
        (𝓝 (inner ℝ (P f) (D φ hφ))) :=
      hsource.congr' (Eventually.of_forall fun m => (hpair (us m) φ hφ).symm)
    exact (tendsto_nhds_unique htarget hsource').trans (hpair f φ hφ).symm
  exact he

def distributionLiftCLM (P : H →L[ℝ] Lp ℝ 2 ν)
    (D : ∀ φ : E → ℝ, regularityTest Set.univ φ → Lp ℝ 2 ν)
    (R : H → (E →ᵇ ℝ)) {K : Set E} (hK : IsCompact K)
    (hRK : ∀ f, tsupport (R f : E → ℝ) ⊆ K)
    (hpair : ∀ f φ hφ, (∫ z, R f z * φ z ∂ν) = inner ℝ (P f) (D φ hφ)) :
    H →L[ℝ] (E →ᵇ ℝ) where
  toLinearMap := distributionLiftLinear ν P D R hK hRK hpair
  cont := distributionLiftLinear_continuous ν P D R hK hRK hpair

/-- The distributional lift is the actual classical derivative whenever
the original L² vector is represented by a smooth compact function. -/
theorem distributionLift_eq_smooth_word {ι : Type*}
    (P : H →L[ℝ] Lp ℝ 2 ν) (v : ι → E) (w : List ι)
    (L : H →L[ℝ] (E →ᵇ ℝ)) {K : Set E} (hK : IsCompact K)
    (hLK : ∀ f, tsupport (L f : E → ℝ) ⊆ K)
    (hpair : ∀ f φ, regularityTest Set.univ φ →
      (∫ z, L f z * φ z ∂ν) = (-1 : ℝ)^w.length *
        ∫ z, P f z * regularityCoefficientWord v w.reverse φ z ∂ν)
    (f : H) (F : E → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hFAE : F =ᵐ[ν] (P f : E → ℝ)) (z : E) :
    L f z = regularityCoefficientWord v w F z := by
  have hword := regularityCoefficientWord_regular v hF hcF w
  let W : E →ᵇ ℝ := ofCompactSupport (regularityCoefficientWord v w F)
    hword.1.continuous hword.2.1
  have he : L f = W := by
    apply compactBCF_eq_of_test_pairings ν (hK.union hcF) (L f) W
      ((hLK f).trans Set.subset_union_left)
      (hword.2.2.trans Set.subset_union_right)
    intro φ hφ
    rw [hpair f φ hφ]
    change _ = ∫ z, regularityCoefficientWord v w F z * φ z ∂ν
    rw [regularityCoefficientWord_integral_transpose ν v F hF w hφ.1 hφ.2.1]
    congr 1
    exact integral_congr_ae (hFAE.symm.mono fun y hy => congrArg (· * _) hy)
  exact congrArg (fun b : E →ᵇ ℝ => b z) he

end Yau.NodeProofs.P06Aux.ScalarSmooth
