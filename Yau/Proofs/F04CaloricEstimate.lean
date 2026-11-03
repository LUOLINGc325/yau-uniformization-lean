import Yau.Proofs.F04FiniteMassTemporal
import Yau.Proofs.F04MassErrorIntegral
import Yau.Proofs.F04CutoffVanishing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem finite_caloric_mass_estimate (hG02 : G02) {n : ℕ}
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T C β : ℝ} {k : ℕ} (hT : 0 < T) (hC : 0 < C) (hβ : 0 < β) (hk : 2 * n ≤ k)
    {χ z : STF X} (hχ : SmoothSpaceC1Time χ (Icc 0 T)) (hz : SmoothSpaceTime z (Icc 0 T))
    (hdata : ∀ x t, t ∈ Icc 0 T →
      0 < χ x t ∧ χ x t ≤ C * (u x) ^ (-(k : ℤ)) ∧
      gradNormSq X.metric.form (fun y => χ y t) x ≤ (C * χ x t / u x) ^ 2 ∧
      HermLE (levi (fun y => χ y t) x) (((C * χ x t : ℝ) : ℂ) • gMat (h t) x) ∧
      (0 < t → deriv (χ x) t ≤ C * (1 + t ^ (β - 1)) * χ x t))
    (hzbound : ∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t)
    (hcal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) z x t = 0) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc 0 T,
      (∫ x, massCutoff u R x * (z x s * χ x s * density ρ x s) ∂μ) ≤
        (E / R) * s * Real.exp ((((n : ℝ) + 1) * C) * (s + s ^ β / β)) := by
  obtain ⟨D, B, hD, hB, herr⟩ := flow_mass_error_integral X o h U P ρ hloc u hu μ hμ hT
  let E := (n : ℝ) * (D + C ^ 2 + D ^ 2) * C * B
  let A := ((n : ℝ) + 1) * C
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨E, hE, ?_⟩
  intro R hR s hs
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let I : ℝ → ℝ := fun t => ∫ x, massCutoff u R x * (z x t * χ x t * density ρ x t) ∂μ
  let J : ℝ → ℝ := fun t => ∫ x, massCutoff u R x *
    ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
      scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ∂μ
  have hder := flow_cutoff_mass_derivative X o h U P ρ hloc μ hμ hT hz hχ u hu hRp
  have hIpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ I t := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (massCutoff_range u R x).1
      (mul_nonneg (mul_nonneg (hzbound x t ht).1 (hdata x t ht).1.le) (density_pos ρ x t).le)
  have hz0 := dominated_caloric_initial_zero X o h U P ρ hloc hT.le hzbound
  have hI0 : I 0 = 0 := by simp only [I, hz0, zero_mul, mul_zero, integral_zero]
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      J t ≤ A * (1 + t ^ (β - 1)) * I t + E / R := by
    have htC : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    obtain ⟨μt, hμt, _⟩ := hG02 n X.manifold (h t)
      (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1.le)
    have he := herr (fun x => χ x t) C k hC hk (hχ.1 t htC)
      (fun x => (hdata x t htC).1) (fun x => (hdata x t htC).2.1)
      (fun x => (hdata x t htC).2.2.1) R hR t htC (fun x => z x t)
      ((smoothSpaceTime_c1 hz).1 t htC) (fun x => hzbound x t htC)
    have htime := finite_mass_time_bound X o h U P ρ hloc (T := T) (t := t) (R := R)
      (a := C * (1 + t ^ (β - 1))) (C := C) ht μ μt hμ hμt u hu hRp hz hχ
      (fun x => hcal x t htC) (fun x => (hzbound x t htC).1)
      (fun x => (hdata x t htC).1.le)
      (fun x => (hdata x t htC).2.2.2.2 ht.1)
      (fun x => (hdata x t htC).2.2.2.1) he.1
    have hcoef := caloric_mass_coefficient_bound (n := n) hC.le
      (Real.rpow_nonneg ht.1.le (β - 1)) (hIpos t htC)
    calc
      J t ≤ ((n : ℝ) * C + C * (1 + t ^ (β - 1))) * I t +
          ∫ x, |z x t * massScalarError (h t) u (fun y => χ y t) R x * density ρ x t| ∂μ := htime
      _ ≤ A * (1 + t ^ (β - 1)) * I t + E / R := add_le_add hcoef he.2
  exact finite_cutoff_gronwall hT.le hA hβ (div_nonneg hE hRp.le) hder.1 hI0
    (fun t ht => hder.2 t ht) hbound s hs

end Yau.F04Proof
