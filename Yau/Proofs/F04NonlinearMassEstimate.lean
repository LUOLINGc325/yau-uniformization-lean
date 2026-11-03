import Yau.Proofs.F04NonlinearMassTemporal
import Yau.Proofs.F04FlowOpenTimeMass
import Yau.Proofs.F04CaloricEstimate

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The nonlinear exponential mass satisfies the ACTUAL finite-radius
 Gronwall estimate BEFORE any radius limit. Initial continuity suffices;
 the cancellation retains w in the spatial adjoint/error and exp(w)-1
 in the nonnegative mass. -/
theorem finite_nonlinear_mass_estimate
    (hG02 : G02) {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T C β : ℝ} {k : ℕ} (hT : 0 < T) (hC : 0 < C) (hβ : 0 < β) (hk : 2*n ≤ k)
    {χ w : STF X} (hχ : SmoothSpaceC1Time χ (Icc 0 T)) (hw : SmoothSpaceTime w (Ioo 0 T))
    (hwC : ContinuousOn (fun p : Pt X × ℝ => w p.1 p.2) (univ ×ˢ Icc 0 T))
    (hInitial : ∀ x, w x 0 = 0)
    (hdata : ∀ x t, t ∈ Icc 0 T →
      0 < χ x t ∧ χ x t ≤ C*(u x)^(-(k : ℤ)) ∧
      gradNormSq X.metric.form (fun y => χ y t) x ≤ (C*χ x t/u x)^2 ∧
      HermLE (levi (fun y => χ y t) x) (((C*χ x t : ℝ) : ℂ) • gMat (h t) x) ∧
      (0 < t → deriv (χ x) t ≤ C*(1+t^(β-1))*χ x t))
    (hwBound : ∀ x t, t ∈ Icc 0 T → 0 ≤ w x t ∧ w x t ≤ ρ x t)
    (hEq : ∀ x t, t ∈ Ioo 0 T → deriv (w x) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
      (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc 0 T,
      (∫ x, massCutoff u R x*((Real.exp (w x s)-1)*χ x s*density ρ x s) ∂μ) ≤
        (E/R)*s*Real.exp ((((n : ℝ)+1)*C)*(s+s^β/β)) := by
  obtain ⟨D,B,hD,hB,herr⟩ := flow_mass_error_integral X o h U P ρ hloc u hu μ hμ hT
  let E := (n : ℝ) * (D + C ^ 2 + D ^ 2) * C * B
  let A := ((n : ℝ)+1)*C
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let z : STF X := fun x t => Real.exp (w x t)-1
  have hzC : ContinuousOn (fun p : Pt X × ℝ => z p.1 p.2) (univ ×ˢ Icc 0 T) :=
    (Real.continuous_exp.comp_continuousOn hwC).sub continuousOn_const
  have hzc : SmoothSpaceC1Time z (Ioo 0 T) := smoothSpaceTime_c1 (fun c => (hw c).exp.sub contDiffOn_const)
  have hwc := smoothSpaceTime_c1 hw
  refine ⟨E,hE,?_⟩
  intro R hR s hs
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let I : ℝ → ℝ := fun t => ∫ x, massCutoff u R x*(z x t*χ x t*density ρ x t) ∂μ
  let J : ℝ → ℝ := fun t => ∫ x, massCutoff u R x*
    ((deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
      scalarCurvature (h t) x*(z x t*χ x t*density ρ x t)) ∂μ
  have hder := flow_cutoff_mass_derivative_openTime X o h U P ρ hloc μ hμ hT hzC hzc hχ u hu hRp
  have hIpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ I t := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (massCutoff_range u R x).1 (mul_nonneg
      (mul_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (hwBound x t ht).1)) (hdata x t ht).1.le)
      (density_pos ρ x t).le)
  have hI0 : I 0 = 0 := by
    simp only [I,z,hInitial,Real.exp_zero,sub_self,zero_mul,mul_zero,integral_zero]
  have hBound (t : ℝ) (ht : t ∈ Ioo 0 T) : J t ≤ A*(1+t^(β-1))*I t+E/R := by
    have htC := Ioo_subset_Icc_self ht
    obtain ⟨μt,hμt,_⟩ := hG02 n X.manifold (h t)
      (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1.le)
    have he := herr (fun x => χ x t) C k hC hk (hχ.1 t htC)
      (fun x => (hdata x t htC).1) (fun x => (hdata x t htC).2.1)
      (fun x => (hdata x t htC).2.2.1) R hR t htC (fun x => w x t)
      (hwc.1 t ht) (fun x => hwBound x t htC)
    have hTime := finite_nonlinear_mass_time_bound X o h U P ρ hloc
      (T := T) (t := t) (R := R) (a := C*(1+t^(β-1))) (C := C) ht μ μt hμ hμt u hu hRp
      hw hχ hC.le (fun x => (hwBound x t htC).1) (fun x => (hdata x t htC).1.le)
      (fun x => (hdata x t htC).2.2.2.2 ht.1) (fun x => hEq x t ht)
      (fun x => (hdata x t htC).2.2.2.1) he.1
    have hCoef := caloric_mass_coefficient_bound (n := n) hC.le
      (Real.rpow_nonneg ht.1.le (β-1)) (hIpos t htC)
    calc
      J t ≤ ((n : ℝ)*C+C*(1+t^(β-1)))*I t+
          ∫ x, |w x t*massScalarError (h t) u (fun y => χ y t) R x*density ρ x t| ∂μ := hTime
      _ ≤ A*(1+t^(β-1))*I t+E/R := add_le_add hCoef he.2
  exact finite_cutoff_gronwall hT.le hA hβ (div_nonneg hE hRp.le) hder.1 hI0
    (fun t ht => hder.2 t ht) hBound s hs

end Yau.F04Proof
