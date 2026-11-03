import Yau.LeafProofs.L17GaussianClosedTimeJets
import Yau.LeafProofs.L17LocalizedSchauderLocalData

/-! The four actual Gaussian jets satisfy the local closed-FTC input data. -/

open Set Metric
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def gaussianLocalFunction (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Space n × Time T) : ℝ :=
  localGaussian P T hT f p (q.1,(q.2 : ℝ))

def gaussianLocalGradient (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Space n × Time T) : D1 n :=
  spatialD (localGaussian P T hT f p) (q.1,(q.2 : ℝ))

def gaussianLocalHessian (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Space n × Time T) : D2 n :=
  spatialDD (localGaussian P T hT f p) (q.1,(q.2 : ℝ))

def gaussianLocalTime (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Space n × Time T) : ℝ :=
  timeD (cylinder Set.univ 0 T) (localGaussian P T hT f p) (q.1,(q.2 : ℝ))

theorem gaussian_local_true_jets (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ)
    (hu : ∀ p, C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p)) :
    LocalTrueJets P T hT (gaussianLocalFunction P T hT f) (gaussianLocalGradient P T hT f)
      (gaussianLocalHessian P T hT f) (gaussianLocalTime P T hT f) := by
  have hc : Continuous (fun q : Space n × Time T => (q.1,(q.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hMap : MapsTo (fun q : Space n × Time T => (q.1,(q.2 : ℝ)))
      (ball (0 : Space n) (2*P.radius) ×ˢ Set.univ) (cylinder Set.univ 0 T) :=
    fun q _ => ⟨mem_univ _,q.2.property⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro p
    exact ⟨(hu p).1.comp hc.continuousOn hMap,(hu p).2.1.comp hc.continuousOn hMap,
      (hu p).2.2.1.comp hc.continuousOn hMap,(hu p).2.2.2.1.comp hc.continuousOn hMap⟩
  · intro p z _ t
    have hspace := (hu p).2.2.2.2.1 (z,(t : ℝ)) ⟨mem_univ _,t.property⟩
    refine ⟨(hspace.differentiableAt (by norm_num)).hasFDerivAt,?_⟩
    exact ((hspace.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  · intro p z _ t
    exact c2_restricted_time_hasDerivWithinAt hT (hu p) z t
  · intro p z _
    exact localGaussian_initial P T hT f p z

theorem gaussian_local_scaled_jet_bounds (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius^2) {γ K : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hK : 0 ≤ K)
    (f : HolderSpace P T γ)
    (hSch : ∀ p : P.centers, SchauderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (P.charts.frozenHeatDuhamel p (L17SourceLocalizationAux.rescaledSource P T hT.le f p)) (K*‖f‖))
    (hLow : ∀ p : P.centers, HolderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (fun q => (P.charts.frozenHeatDuhamel p (L17SourceLocalizationAux.rescaledSource P T hT.le f p) q,
        spatialD (P.charts.frozenHeatDuhamel p (L17SourceLocalizationAux.rescaledSource P T hT.le f p)) q))
      (K*‖f‖*((T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ)/2)))) :
    LocalScaledJetBounds P T γ (4*K*‖f‖) (gaussianLocalFunction P T hT.le f)
      (gaussianLocalGradient P T hT.le f) (gaussianLocalHessian P T hT.le f)
      (gaussianLocalTime P T hT.le f) := by
  let J := K*‖f‖*((T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ)/2))
  have hS : 0 ≤ T/P.radius^2 := (div_pos hT (sq_pos_of_pos P.radius_pos)).le
  have hSone : T/P.radius^2 ≤ 1 := (div_le_one (sq_pos_of_pos P.radius_pos)).mpr hSmall
  have hJ : J ≤ 2*K*‖f‖ := by
    have hfirst := Real.rpow_le_one hS hSone (by norm_num : (0 : ℝ) ≤ 1/2)
    have hsecond := Real.rpow_le_one hS hSone (by linarith : 0 ≤ (1-γ)/2)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (mul_nonneg hK (norm_nonneg f))
    dsimp only [J]
    nlinarith
  have hJtwo : 2*J ≤ 4*K*‖f‖ := by linarith
  have hCtwo : 2*(K*‖f‖) ≤ 4*K*‖f‖ := by nlinarith [mul_nonneg hK (norm_nonneg f)]
  have hCone : K*‖f‖ ≤ 4*K*‖f‖ := by nlinarith [mul_nonneg hK (norm_nonneg f)]
  have hJone : J ≤ 4*K*‖f‖ := by nlinarith [mul_nonneg hK (norm_nonneg f)]
  have hρ : 0 ≤ P.radius := P.radius_pos.le
  have hPoint : ∀ q : Space n × Time T, (q.1,(q.2 : ℝ)) ∈ cylinder Set.univ 0 T :=
    fun q => ⟨mem_univ _,q.2.property⟩
  constructor
  · intro p q _
    have h := parabolicUnscale_four_jet_bounds P.radius_pos hT hγ (hSch p) (hLow p)
    simp only [← localGaussian_eq_unscale P T hT.le f p] at h
    obtain ⟨hv,hD,hH,hb⟩ := h.2.1 _ (hPoint q)
    refine ⟨hv.trans ?_,hD.trans ?_,hH.trans hCone,hb.trans hCone⟩
    · exact mul_le_mul_of_nonneg_left hJone (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left hJone P.radius_pos.le
  · intro p q r _ _
    have h := parabolicUnscale_four_jet_bounds P.radius_pos hT hγ (hSch p) (hLow p)
    simp only [← localGaussian_eq_unscale P T hT.le f p] at h
    obtain ⟨hv,hD,hH,hb⟩ := h.2.2 _ (hPoint q) _ (hPoint r)
    have hd : 0 ≤ (localScaledDistance P.radius q r)^γ := Real.rpow_nonneg
      (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _
    change _ ≤ (2*P.radius^2*J)*(localScaledDistance P.radius q r)^γ at hv
    change _ ≤ (2*P.radius*J)*(localScaledDistance P.radius q r)^γ at hD
    change _ ≤ (2*(K*‖f‖))*(localScaledDistance P.radius q r)^γ at hH hb
    refine ⟨hv.trans ?_,hD.trans ?_,hH.trans ?_,hb.trans ?_⟩
    · calc
        _ = P.radius^2*(2*J)*(localScaledDistance P.radius q r)^γ := by ring
        _ ≤ _ := by gcongr
    · calc
        _ = P.radius*(2*J)*(localScaledDistance P.radius q r)^γ := by ring
        _ ≤ _ := by gcongr
    · exact mul_le_mul_of_nonneg_right hCtwo hd
    · exact mul_le_mul_of_nonneg_right hCtwo hd

end Yau.LeafProofs.L17Aux
