import Yau.LeafProofs.L16UniformDifferenceEnergy

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem localEnergy_homogeneous_spatial_weak_derivative_gain {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r) (i j : Yau.RIdx n) :
    ∃ Z : Point n → ℝ, MemLp Z 2 (volume.restrict V) ∧
      ∀ φ : Point n → ℝ, Test V φ →
        (∫ p, G p j*d (fun x => φ (x,p.2)) p.1 i ∂volume.restrict V) =
          -(∫ p, Z p*φ p ∂volume.restrict V) := by
  let Q : Set (Point n) := O ×ˢ Set.Ioo l r
  have hQ : IsOpen Q := hO.prod isOpen_Ioo
  obtain ⟨θ,hθ,hθRange,hθNear⟩ := exists_bounded_test_eq_one_near_compact hQ hVC hVQ
  have hθOne (p : Point n) (hp : p ∈ V) : θ p = 1 :=
    (hθNear p (subset_closure hp)).eq_of_nhds
  have hVK : V ⊆ tsupport θ := by
    intro p hp
    apply subset_tsupport θ
    change θ p ≠ 0
    rw [hθOne p hp]
    exact one_ne_zero
  obtain ⟨η,hη,hηNear⟩ := exists_test_eq_one_near_compact hQ hθ.2.1 hθ.2.2
  obtain ⟨a',c',C,hC,ha',hca',hc',hAgree,hAVal,hADq,hCVal,hCDq⟩ :=
    exists_compact_coefficient_extensions hQ hθ.2.1 hθ.2.2 hSmooth
  obtain ⟨U,hU,hKU,hUQ,hCommon⟩ := exists_open_common_agreement hQ hθ.2.2 hηNear
    (fun p hp => (hAgree p hp).1) (fun p hp => (hAgree p hp).2)
  let w0 : Point n → ℝ := fun p => η p*u p
  let H0 : Point n → Yau.RIdx n → ℝ := localizedWeakGradient η u G
  let P0 : Point n → Yau.RIdx n → ℝ := localizedWeakFlux η a G
  let R0 : Point n → ℝ := localizedWeakSource η u a b G
  obtain ⟨hw0,hcw0,hH0,hP0,hR0,hcR0,hGrad0,hEq0⟩ := localizedWeakFields_regular hO hSmooth hE hEq hη
  have hPlateau (p : Point n) (hp : p ∈ U) :
      (∀ k, H0 p k = G p k) ∧ (∀ k, P0 p k = energyFlux a' H0 p k) ∧
        R0 p = ∑ k, c' p k*H0 p k :=
    localizedWeakFields_eq_on_open_plateau hU hη (fun q hq => (hCommon q hq).1)
      (fun q hq => (hCommon q hq).2.1) (fun q hq => (hCommon q hq).2.2) u G hp
  have hEllU : Elliptic U a' lam upper := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro p hp
    rw [(hCommon p hp).2.1]
    exact hEll.2.2 p (hUQ hp)
  have hθU : Test U θ := ⟨hθ.1,hθ.2.1,hKU⟩
  obtain ⟨M,hM,_hθValue,hθDeriv,_hθLip⟩ := smooth_compact_global_bounds hθ.1 hθ.2.1
  have hJet (p e : Point n) (he : ‖e‖ = 1) : |fderiv ℝ θ p e| ≤ M := by
    calc
      _ = ‖fderiv ℝ θ p e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ θ p‖*‖e‖ := (fderiv ℝ θ p).le_opNorm e
      _ ≤ M := by rw [he,mul_one]; exact hθDeriv p
  have hTime (p : Point n) : |fderiv ℝ θ p (0,1)| ≤ M := hJet p _ (by simp [Prod.norm_def])
  have hSpace (p : Point n) (k : Yau.RIdx n) : |fderiv ℝ θ p (Yau.realVec k,0)| ≤ M :=
    hJet p _ (by simp only [Prod.norm_def,realVec_norm,norm_zero,max_eq_left (by norm_num : (0 : ℝ) ≤ 1)])
  have hθBound (p : Point n) : |θ p| ≤ 1 := by
    rw [abs_of_nonneg (hθRange p).1]
    exact (hθRange p).2
  obtain ⟨B,hB,hBound⟩ := exists_uniform_difference_energy_constant n lam upper C M hEll.1 hC.le hM.le
  obtain ⟨δ,hδ,hShift⟩ := compact_spatial_shift_radius hθ.2.1 hU hKU
  let E : ℝ := ∫ p, ∑ k, (H0 p k)^2
  have hEPos : 0 ≤ E := integral_nonneg (fun p => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hWeighted (h : ℝ) (hh : h ≠ 0) (hSmall : |h| < δ) :
      (∫ p, (θ p)^2*(∑ k, (spatialDifferenceQuotient (fun q => H0 q k) (Yau.realVec i) h p)^2)) ≤ B*E := by
    apply hBound U a' c' θ w0 H0 P0 R0 hEllU ha' (fun k => (hc' k).1)
      hAVal hCVal hADq hCDq hθU hθBound hTime hSpace hw0
      (fun k => (hH0 k).1) (fun k => (hP0 k).1) hR0 hcw0
      (fun k => (hH0 k).2) (fun k => (hP0 k).2) hcR0 hGrad0 hEq0
      (fun p hp => (hPlateau p hp).2.1) (fun p hp => (hPlateau p hp).2.2) i h hh
    intro p hp
    exact hShift p hp (h • Yau.realVec i) (by simpa only [norm_smul,Real.norm_eq_abs,realVec_norm,mul_one] using hSmall)
  have hcθ2 : HasCompactSupport (fun p => (θ p)^2) := by
    have h : HasCompactSupport (fun p => θ p*θ p) := hθ.2.1.mul_right
    simpa only [pow_two] using h
  have hθTop : MemLp (fun p => (θ p)^2) (⊤ : ENNReal) volume :=
    (hθ.1.pow 2).continuous.memLp_top_of_hasCompactSupport hcθ2 _
  have hLocalBound (h : ℝ) (hh : h ≠ 0) (hSmall : |h| < δ) :
      (∫ p, (spatialDifferenceQuotient (fun q => H0 q j) (Yau.realVec i) h p)^2 ∂volume.restrict V) ≤ B*E := by
    let Hd : Point n → Yau.RIdx n → ℝ := fun p k => spatialDifferenceQuotient (fun q => H0 q k) (Yau.realVec i) h p
    have hHd (k : Yau.RIdx n) : MemLp (fun p => Hd p k) 2 volume :=
      memLp_spatialDifferenceQuotient (hH0 k).1 (Yau.realVec i) h
    have hEach (k : Yau.RIdx n) : Integrable (fun p => (θ p)^2*(Hd p k)^2) volume := by
      have hW := integrable_weighted_mul_of_memLp hθTop (hHd k) (hHd k)
      convert! hW using 1
      ext p
      ring
    have hInt : Integrable (fun p => (θ p)^2*(∑ k, (Hd p k)^2)) volume := by
      have hS := integrable_finsetSum Finset.univ (fun k _ => hEach k)
      simpa only [Finset.mul_sum] using hS
    have hJ2 : Integrable (fun p => (Hd p j)^2) (volume.restrict V) := by
      have hJ := (hHd j).restrict V
      have hJ' := (memLp_two_iff_integrable_sq_norm hJ.aestronglyMeasurable).mp hJ
      simpa only [Real.norm_eq_abs,sq_abs] using hJ'
    have hInd : Integrable (V.indicator (fun p => (Hd p j)^2)) volume :=
      (integrable_indicator_iff hV.measurableSet).2 hJ2
    calc
      _ = ∫ p, V.indicator (fun q => (Hd q j)^2) p := (integral_indicator hV.measurableSet).symm
      _ ≤ ∫ p, (θ p)^2*(∑ k, (Hd p k)^2) := by
        apply integral_mono hInd hInt
        intro p
        dsimp only
        by_cases hp : p ∈ V
        · rw [Set.indicator_of_mem hp,hθOne p hp,one_pow,one_mul]
          exact Finset.single_le_sum (s := Finset.univ) (f := fun k => (Hd p k)^2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ j)
        · rw [Set.indicator_of_notMem hp]
          positivity
      _ ≤ B*E := hWeighted h hh hSmall
  let steps : ℕ → ℝ := fun k => (δ/2)*(1/2 : ℝ)^k
  have hStepsPos (k : ℕ) : 0 < steps k := mul_pos (by positivity) (pow_pos (by norm_num) k)
  have hStepsSmall (k : ℕ) : |steps k| < δ := by
    rw [abs_of_pos (hStepsPos k)]
    have hP : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hLe := mul_le_mul_of_nonneg_left hP (show 0 ≤ δ/2 by positivity)
    dsimp only [steps]
    nlinarith
  have hStepsLim : Tendsto steps atTop (𝓝 0) := by
    have hP := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_mul (δ/2)
    simpa only [mul_zero] using hP
  have hBE : 0 ≤ B*E := mul_nonneg hB.le hEPos
  obtain ⟨Z,hZ,_hZBound,hZWeak⟩ :=
    exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_sq_bound hV (Yau.realVec i)
      (hH0 j).1 (Real.sqrt (B*E)) (Real.sqrt_nonneg _) (fun k => (hStepsPos k).ne') hStepsLim
      (fun k => by rw [Real.sq_sqrt hBE]; exact hLocalBound (steps k) (hStepsPos k).ne' (hStepsSmall k))
  refine ⟨Z,hZ,?_⟩
  intro φ hφ
  simp_rw [d_eq_joint_fderiv (hφ.1.differentiable (by simp) _) i]
  have hIdent : (∫ p, G p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
      ∫ p, H0 p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
    rw [(hPlateau p (hKU (hVK hp))).1 j]
  exact hIdent.trans (hZWeak φ hφ)

end Yau.LeafProofs.L16Aux
