import Yau.LeafProofs.L23FieldMetricGaussVariation

/-! The first variation of actual geodesic energy allows both endpoints to move. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem chartGeodesic_variation_firstVariation
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (ζ : ℝ × ℝ → ComplexVector n × ComplexVector n)
    {a ε E' : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hζ : ContDiffOn ℝ 2 ζ (Set.Ioo (-a) a ×ˢ Set.Ioo (-ε) (1+ε)))
    (hs : ∀ r ∈ Set.Ioo (-a) a, ∀ u ∈ Set.Ioo (-ε) (1+ε),
      (ζ (r,u)).1 ∈ chartTarget c ∧
        HasDerivAt (fun t => ζ (r,t)) (chartGeodesicSpray h c (ζ (r,u))) u)
    (henergy : HasDerivAt (fun r => chartGeodesicEnergy h c (ζ (r,0))) E' 0) :
    2*(realMetricInChart h c (ζ (0,1)).1 (ζ (0,1)).2 (deriv (fun r => (ζ (r,1)).1) 0)-
      realMetricInChart h c (ζ (0,0)).1 (ζ (0,0)).2 (deriv (fun r => (ζ (r,0)).1) 0)) = E' := by
  let I := Set.Ioo (-a) a
  let J := Set.Ioo (-ε) (1+ε)
  let Z : ℝ × ℝ → ComplexVector n := fun p => (ζ p).1
  let T : ℝ × ℝ → ComplexVector n := fun p => (ζ p).2
  let V : ℝ → ComplexVector n := fun u => deriv (fun r => Z (r,u)) 0
  let W : ℝ → ComplexVector n := fun u => deriv (fun r => T (r,u)) 0
  have h₀I : (0 : ℝ) ∈ I := ⟨by linarith,ha⟩
  have h₀J : (0 : ℝ) ∈ J := ⟨by linarith,by linarith⟩
  have h₁J : (1 : ℝ) ∈ J := by constructor <;> linarith
  have hDopen : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
  have hZ : ContDiffOn ℝ 2 Z (I ×ˢ J) := hζ.fst
  have hT : ContDiffOn ℝ 2 T (I ×ˢ J) := hζ.snd
  have hZtime (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => Z (0,s)) (T (0,u)) u := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u
      (hs 0 h₀I u hu).2 using 1
  have hTtime (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => T (0,s))
        (-chartChristoffelBilin h c (Z (0,u)) (T (0,u)) (T (0,u))) u := by
    convert! (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u
      (hs 0 h₀I u hu).2 using 1
    exact (chartGeodesicAcceleration_eq h c (Z (0,u)) (T (0,u))).symm
  have hRZ (u : ℝ) (hu : u ∈ J) : HasDerivAt (fun r => Z (r,u)) (V u) 0 := by
    exact (((hZ.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
  have hRT (u : ℝ) (hu : u ∈ J) : HasDerivAt (fun r => T (r,u)) (W u) 0 := by
    exact (((hT.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
  have hVtime (u : ℝ) (hu : u ∈ J) : HasDerivAt V (W u) u := by
    apply mixed_parameter_velocity_hasDerivAt (hZ.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩))
    filter_upwards [hDopen.mem_nhds ⟨h₀I,hu⟩] with p hp
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt p.2
      (hs p.1 hp.1 p.2 hp.2).2 using 1
  have hEpair (u : ℝ) (hu : u ∈ J) :
      realMetricInChart h c (Z (0,u)) (T (0,u))
        (W u+chartChristoffelBilin h c (Z (0,u)) (T (0,u)) (V u)) = E'/2 := by
    have H := chartEnergy_variation_hasDerivAt h hh c
      (z := fun r => Z (r,u)) (T := fun r => T (r,u)) (t := 0)
      (J := V u) (T' := W u) (hs 0 h₀I u hu).1 (hRZ u hu) (hRT u hu)
    have hEq : (fun r => chartGeodesicEnergy h c (ζ (r,0))) =ᶠ[𝓝 (0 : ℝ)]
        (fun r => realMetricInChart h c (Z (r,u)) (T (r,u)) (T (r,u))) := by
      filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
      exact chartGeodesicEnergy_constant h hh c (fun s => ζ (r,s)) (hs r hr) h₀J hu
    have HE := (H.congr_of_eventuallyEq hEq).unique henergy
    rw [chartChristoffelBilin_symm h c (Z (0,u)) (V u) (T (0,u))] at HE
    linarith
  have hP (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => realMetricInChart h c (Z (0,s)) (T (0,s)) (V s)) (E'/2) u := by
    have H := chartGeodesic_pairing_hasDerivAt h hh c
      (z := fun s => Z (0,s)) (T := fun s => T (0,s)) (J := V) (t := u) (J' := W u)
      (hs 0 h₀I u hu).1 (hZtime u hu) (hTtime u hu) (hVtime u hu)
    rw [hEpair u hu] at H
    exact H
  have hPdiff (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => realMetricInChart h c (Z (0,s)) (T (0,s)) (V s)-s*(E'/2)) 0 u := by
    convert! (hP u hu).sub ((hasDerivAt_id u).mul_const (E'/2)) using 1 <;> simp
  have H := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) (1+ε)).isPreconnected
    (fun u hu => (hPdiff u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hPdiff u hu).deriv) h₁J h₀J
  change realMetricInChart h c (ζ (0,1)).1 (ζ (0,1)).2 (deriv (fun r => (ζ (r,1)).1) 0)-1*(E'/2) =
    realMetricInChart h c (ζ (0,0)).1 (ζ (0,0)).2 (deriv (fun r => (ζ (r,0)).1) 0)-0*(E'/2) at H
  linarith

end Yau.LeafProofs.L23Aux
