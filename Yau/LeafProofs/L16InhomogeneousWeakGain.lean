import Yau.LeafProofs.L16InhomogeneousDifferenceEnergy
import Yau.LeafProofs.L16WeakSobolevCalculus

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem inhomogeneous_global_weak_fields_spatial_derivative_gain {n : ℕ}
    {Q V : Set (Point n)} (hQ : IsOpen Q) (hV : IsOpen V)
    (hVC : IsCompact (closure V)) (hVQ : closure V ⊆ Q)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {lam upper C : ℝ}
    (hC : 0 ≤ C) (hEll : Elliptic Q a lam upper)
    (ha : ContDiff ℝ ∞ a) (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hAVal : ∀ p, ‖a p‖ ≤ C) (hCVal : ∀ j p, |c p j| ≤ C)
    (hADq : ∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C)
    (hCDq : ∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C)
    {w R f : Point n → ℝ} {H P F J : Point n → Yau.RIdx n → ℝ}
    {K : Yau.RIdx n → Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hH : ∀ j, MemLp (fun p => H p j) 2 volume)
    (hP : ∀ j, MemLp (fun p => P p j) 2 volume) (hR : MemLp R 2 volume)
    (hcw : HasCompactSupport w) (hcH : ∀ j, HasCompactSupport (fun p => H p j))
    (hcP : ∀ j, HasCompactSupport (fun p => P p j)) (hcR : HasCompactSupport R)
    (hGrad : WeakGradient Set.univ Set.univ w H)
    (hEq : WeakDivergenceEvolution Set.univ Set.univ w P R)
    (hF : ∀ j, MemLp (fun p => F p j) 2 volume) (hf : MemLp f 2 volume)
    (hK : ∀ j k, MemLp (fun p => K j p k) 2 volume) (hJ : ∀ k, MemLp (fun p => J p k) 2 volume)
    (hcF : ∀ j, HasCompactSupport (fun p => F p j)) (hcf : HasCompactSupport f)
    (hcK : ∀ j k, HasCompactSupport (fun p => K j p k)) (hcJ : ∀ k, HasCompactSupport (fun p => J p k))
    (hGradF : ∀ j, WeakGradient Set.univ Set.univ (fun p => F p j) (K j))
    (hGradf : WeakGradient Set.univ Set.univ f J)
    (hFlux : ∀ p ∈ Q, ∀ j, P p j = energyFlux a H p j+F p j)
    (hSource : ∀ p ∈ Q, R p = (∑ j, c p j*H p j)+f p)
    (i j : Yau.RIdx n) :
    ∃ Z : Point n → ℝ, MemLp Z 2 (volume.restrict V) ∧
      ∀ φ : Point n → ℝ, Test V φ →
        (∫ p, H p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
          -(∫ p, Z p*φ p ∂volume.restrict V) := by
  obtain ⟨θ,hθ,hθRange,hθNear⟩ := exists_bounded_test_eq_one_near_compact hQ hVC hVQ
  have hθOne (p : Point n) (hp : p ∈ V) : θ p = 1 :=
    (hθNear p (subset_closure hp)).eq_of_nhds
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
  obtain ⟨B,hB,hBound⟩ := exists_uniform_inhomogeneous_difference_energy_constant n lam upper C M hEll.1 hC hM.le
  obtain ⟨δ,hδ,hShift⟩ := compact_spatial_shift_radius hθ.2.1 hQ hθ.2.2
  let E : ℝ := (∫ p, ∑ k, (H p k)^2)+(∑ j, ∫ p, ∑ k, (K j p k)^2)+(∫ p, ∑ k, (J p k)^2)
  have hEPos : 0 ≤ E := by
    dsimp only [E]
    exact add_nonneg (add_nonneg
      (integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))))
      (integral_nonneg (fun p => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hWeighted (h : ℝ) (hh : h ≠ 0) (hSmall : |h| < δ) :
      (∫ p, (θ p)^2*(∑ k, (spatialDifferenceQuotient (fun q => H q k) (Yau.realVec i) h p)^2)) ≤ B*E := by
    apply hBound Q a c θ w H P R f F J K hEll ha hc hAVal hCVal hADq hCDq
      hθ hθBound hTime hSpace hw hH hP hR hcw hcH hcP hcR hGrad hEq
      hF hf hK hJ hcF hcf hcK hcJ hGradF hGradf hFlux hSource i h hh
    intro p hp
    exact hShift p hp (h • Yau.realVec i) (by simpa only [norm_smul,Real.norm_eq_abs,realVec_norm,mul_one] using hSmall)
  have hcθ2 : HasCompactSupport (fun p => (θ p)^2) := by
    have h : HasCompactSupport (fun p => θ p*θ p) := hθ.2.1.mul_right
    simpa only [pow_two] using h
  have hθTop : MemLp (fun p => (θ p)^2) (⊤ : ENNReal) volume :=
    (hθ.1.pow 2).continuous.memLp_top_of_hasCompactSupport hcθ2 _
  have hLocalBound (h : ℝ) (hh : h ≠ 0) (hSmall : |h| < δ) :
      (∫ p, (spatialDifferenceQuotient (fun q => H q j) (Yau.realVec i) h p)^2 ∂volume.restrict V) ≤ B*E := by
    let Hd : Point n → Yau.RIdx n → ℝ := fun p k => spatialDifferenceQuotient (fun q => H q k) (Yau.realVec i) h p
    have hHd (k : Yau.RIdx n) : MemLp (fun p => Hd p k) 2 volume :=
      memLp_spatialDifferenceQuotient (hH k) (Yau.realVec i) h
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
      (hH j) (Real.sqrt (B*E)) (Real.sqrt_nonneg _) (fun k => (hStepsPos k).ne') hStepsLim
      (fun k => by rw [Real.sq_sqrt hBE]; exact hLocalBound (steps k) (hStepsPos k).ne' (hStepsSmall k))
  exact ⟨Z,hZ,hZWeak⟩

end Yau.LeafProofs.L16Aux
