import Yau.LeafProofs.L23FieldMetricLocalFlow

/-! Actual spray homogeneity rescales a short local flow to unit geodesic time. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold NNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartGeodesicAcceleration_smul (h : HermitianField M) (c : M.Carrier)
    (z v : ComplexVector n) (e : ℝ) :
    chartGeodesicAcceleration h c z (e • v) = e^2 • chartGeodesicAcceleration h c z v := by
  rw [chartGeodesicAcceleration_eq,chartGeodesicAcceleration_eq]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_neg,smul_smul,pow_two]

def normalizedChartFlow (e : ℝ)
    (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (p : ComplexVector n × ComplexVector n) (u : ℝ) : ComplexVector n × ComplexVector n :=
  let z := φ (p.1,e⁻¹ • p.2) (e*u)
  (z.1,e • z.2)

theorem normalizedChartFlow_initial (e : ℝ) (he : e ≠ 0)
    (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (p : ComplexVector n × ComplexVector n)
    (hi : φ (p.1,e⁻¹ • p.2) 0 = (p.1,e⁻¹ • p.2)) :
    normalizedChartFlow e φ p 0 = p := by
  simp only [normalizedChartFlow,mul_zero,hi,smul_smul,mul_inv_cancel₀ he,one_smul]

theorem normalizedChartFlow_hasDerivAt (h : HermitianField M) (c : M.Carrier)
    (e : ℝ) (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (p : ComplexVector n × ComplexVector n) (u : ℝ)
    (hsol : HasDerivAt (φ (p.1,e⁻¹ • p.2))
      (chartGeodesicSpray h c (φ (p.1,e⁻¹ • p.2) (e*u))) (e*u)) :
    HasDerivAt (normalizedChartFlow e φ p)
      (chartGeodesicSpray h c (normalizedChartFlow e φ p u)) u := by
  have H := hsol.scomp u ((hasDerivAt_id u).const_mul e)
  have H₁ : HasDerivAt (fun v => (φ (p.1,e⁻¹ • p.2) (e*v)).1)
      (e • (φ (p.1,e⁻¹ • p.2) (e*u)).2) u := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u H using 1 <;>
      simp [chartGeodesicSpray]
  have H₂ : HasDerivAt (fun v => (φ (p.1,e⁻¹ • p.2) (e*v)).2)
      (e • chartGeodesicAcceleration h c (φ (p.1,e⁻¹ • p.2) (e*u)).1
        (φ (p.1,e⁻¹ • p.2) (e*u)).2) u := by
    convert! (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u H using 1 <;>
      simp [chartGeodesicSpray]
  have H' := H₁.prodMk (H₂.const_smul e)
  convert! H' using 1 <;>
    simp only [chartGeodesicSpray,normalizedChartFlow,chartGeodesicAcceleration_smul,smul_smul,pow_two]

theorem normalizedChartFlow_contDiffOn {k : ℕ∞ω} (e : ℝ)
    (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    {Q D : Set ((ComplexVector n × ComplexVector n) × ℝ)}
    (hφ : ContDiffOn ℝ k (Function.uncurry φ) Q)
    (hmap : ∀ p ∈ D, ((p.1.1,e⁻¹ • p.1.2),e*p.2) ∈ Q) :
    ContDiffOn ℝ k (Function.uncurry (normalizedChartFlow e φ)) D := by
  have hκ : ContDiff ℝ k
      (fun p : (ComplexVector n × ComplexVector n) × ℝ => ((p.1.1,e⁻¹ • p.1.2),e*p.2)) := by
    fun_prop
  have H := hφ.comp hκ.contDiffOn hmap
  convert! H.fst.prodMk (H.snd.const_smul e) using 1

theorem chartGeodesicAcceleration_hasFDerivAt_zero
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget c) :
    HasFDerivAt (fun p : ComplexVector n × ComplexVector n =>
      chartGeodesicAcceleration h c p.1 p.2)
        (0 : (ComplexVector n × ComplexVector n) →L[ℝ] ComplexVector n) (z,0) := by
  have hscalar (i a b : RIdx n) : HasFDerivAt
      (fun p : ComplexVector n × ComplexVector n =>
        christoffel h c p.1 i a b * realCoord p.2 a * realCoord p.2 b)
        (0 : (ComplexVector n × ComplexVector n) →L[ℝ] ℝ) (z,0) := by
    have hΓ := ((christoffel_contDiffOn h hh c i a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).comp
        (z,(0 : ComplexVector n)) contDiffAt_fst
    have ha := (contDiff_realCoord a).contDiffAt.comp (z,(0 : ComplexVector n)) contDiffAt_snd
    have hb := (contDiff_realCoord b).contDiffAt.comp (z,(0 : ComplexVector n)) contDiffAt_snd
    have H := ((hΓ.differentiableAt (by simp)).hasFDerivAt.mul
      ((ha.differentiableAt (by simp)).hasFDerivAt)).mul
        ((hb.differentiableAt (by simp)).hasFDerivAt)
    convert! H using 1 <;> simp [realCoord]
  have hsum (i : RIdx n) := HasFDerivAt.sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun b _ => hscalar i a b))
  have hvec (i : RIdx n) := (hsum i).smul_const (realVec i)
  have H := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hvec i)).neg
  have hzero (v : ComplexVector n) :
      (0 : (ComplexVector n × ComplexVector n) →L[ℝ] ℝ).smulRight v = 0 := by
    apply ContinuousLinearMap.ext
    intro p
    change (0 : ℝ) • v = (0 : ComplexVector n)
    exact zero_smul ℝ v
  have H0 := H
  simp only [Finset.sum_const_zero,hzero,neg_zero] at H0
  convert! H0 using 1
  funext p
  simp only [chartGeodesicAcceleration,Pi.neg_apply,Finset.sum_apply]

theorem chartGeodesicSpray_hasFDerivAt_zero
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget c) :
    HasFDerivAt (chartGeodesicSpray h c)
      ((ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).prod
        (0 : (ComplexVector n × ComplexVector n) →L[ℝ] ComplexVector n)) (z,0) :=
  (hasFDerivAt_snd (p := (z,(0 : ComplexVector n)))).prodMk
    (chartGeodesicAcceleration_hasFDerivAt_zero h hh c z hz)

def zeroSpeedLinearization (n : ℕ) :
    (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n) :=
  (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).prod 0

theorem zeroSpeedLinearization_variation
    (V : ℝ → (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n))
    {ε : ℝ} (hε : 0 < ε) (hi : V 0 = ContinuousLinearMap.id ℝ _)
    (hV : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt V ((zeroSpeedLinearization n).comp (V t)) t)
    (w : ComplexVector n) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    V t (0,w) = (t • w,w) := by
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hlin (s : ℝ) (hs : s ∈ Set.Ioo (-ε) ε) :
      HasDerivAt (fun u => V u (0,w)) ((V s (0,w)).2,0) s := by
    convert! (hV s hs).clm_apply (hasDerivAt_const s ((0,w) : ComplexVector n × ComplexVector n)) using 1 <;>
      simp [zeroSpeedLinearization]
  have hsecondD (s : ℝ) (hs : s ∈ Set.Ioo (-ε) ε) :
      HasDerivAt (fun u => (V u (0,w)).2) 0 s := by
    convert! (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt s (hlin s hs) using 1
  have hsecond (s : ℝ) (hs : s ∈ Set.Ioo (-ε) ε) : (V s (0,w)).2 = w := by
    have H := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun u hu => (hsecondD u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hsecondD u hu).deriv) hs h₀
    simpa only [hi,ContinuousLinearMap.id_apply] using H
  have hfirstD (s : ℝ) (hs : s ∈ Set.Ioo (-ε) ε) :
      HasDerivAt (fun u => (V u (0,w)).1) w s := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt s (hlin s hs) using 1
    exact (hsecond s hs).symm
  have hdiff (s : ℝ) (hs : s ∈ Set.Ioo (-ε) ε) :
      HasDerivAt (fun u => (V u (0,w)).1-u • w) 0 s := by
    convert! (hfirstD s hs).sub ((hasDerivAt_id s).smul_const w) using 1 <;> simp
  have H := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
    (fun u hu => (hdiff u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hdiff u hu).deriv) ht h₀
  have hfirst : (V t (0,w)).1 = t • w := by
    apply sub_eq_zero.mp
    simpa only [hi,ContinuousLinearMap.id_apply,zero_smul,sub_zero] using H
  exact Prod.ext hfirst (hsecond t ht)

theorem zeroSpeed_flow_stationary (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (U : Set (ComplexVector n × ComplexVector n))
    (K : ℝ≥0) (hLip : LipschitzOnWith K (chartGeodesicSpray h c) U)
    (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    {ε : ℝ} (hε : 0 < ε) (hzU : (z,0) ∈ U) (hi : φ (z,0) 0 = (z,0))
    (hs : ∀ t ∈ Set.Ioo (-ε) ε, φ (z,0) t ∈ U ∧
      HasDerivAt (φ (z,0)) (chartGeodesicSpray h c (φ (z,0) t)) t) :
    ∀ t ∈ Set.Ioo (-ε) ε, φ (z,0) t = (z,0) := by
  have hzero : chartGeodesicSpray h c (z,0) = 0 := by
    simp [chartGeodesicSpray,chartGeodesicAcceleration,realCoord]
  have H := ODE_solution_unique_of_mem_Ioo
    (v := fun _ => chartGeodesicSpray h c) (s := fun _ => U) (K := K)
    (fun _ _ => hLip) (show (0 : ℝ) ∈ Set.Ioo (-ε) ε by constructor <;> linarith)
    (f := φ (z,0)) (g := fun _ => ((z,0) : ComplexVector n × ComplexVector n))
    (fun t ht => ⟨(hs t ht).2,(hs t ht).1⟩)
    (fun t _ => ⟨by simpa only [hzero] using hasDerivAt_const t ((z,0) : ComplexVector n × ComplexVector n),hzU⟩) hi
  exact H

theorem zeroSpeed_flow_endpoint_derivative
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget c)
    (φ : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (V : (ComplexVector n × ComplexVector n) → ℝ →
      (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n))
    {ε e : ℝ} (hε : 0 < ε) (he : e ∈ Set.Ioo (-ε) ε)
    (hi : V (z,0) 0 = ContinuousLinearMap.id ℝ _)
    (hzero : ∀ t ∈ Set.Ioo (-ε) ε, φ (z,0) t = (z,0))
    (hV : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (V (z,0))
      ((fderiv ℝ (chartGeodesicSpray h c) (φ (z,0) t)).comp (V (z,0) t)) t)
    (hx : HasFDerivAt (fun p => φ p e) (V (z,0) e) (z,0)) :
    HasFDerivAt (fun v => (φ (z,v) e).1)
      (e • ContinuousLinearMap.id ℝ (ComplexVector n)) 0 := by
  have hlin (t : ℝ) (ht : t ∈ Set.Ioo (-ε) ε) :
      HasDerivAt (V (z,0)) ((zeroSpeedLinearization n).comp (V (z,0) t)) t := by
    have H := hV t ht
    rw [hzero t ht,(chartGeodesicSpray_hasFDerivAt_zero h hh c z hz).fderiv] at H
    exact H
  have H := (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp 0
    (hx.comp 0 ((hasFDerivAt_const (𝕜 := ℝ) z (0 : ComplexVector n)).prodMk (hasFDerivAt_id (0 : ComplexVector n))))
  convert! H using 1
  apply ContinuousLinearMap.ext
  intro w
  change e • w = (V (z,0) e (0,w)).1
  exact (congrArg Prod.fst (zeroSpeedLinearization_variation (V (z,0)) hε hi hlin w he)).symm

end Yau.LeafProofs.L23Aux
