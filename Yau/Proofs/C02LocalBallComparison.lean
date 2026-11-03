import Yau.Proofs.C02TangentNormComparison
import Yau.Proofs.C02CurveDistanceBound
import Yau.Proofs.C02FirstExit
import Yau.LeafProofs.L12HopfRinow
import Yau.LeafProofs.L23FieldMetric

/-! A first-exit argument compares the actual two distance balls using
quadratic-form control only on the older ball. -/

noncomputable section
open Set
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem newer_unit_ball_subset_older_two_ball (g₀ g₁ : SmoothMetric M)
    (p : M.Carrier)
    (hCompare : ∀ x, inducedDistance g₀.form p x ≤ 2 →
      ∀ v : TangentVector M x,
        hermitianNormSq (g₀.form x) v ≤ (3 / 2 : ℝ) ^ 2 * hermitianNormSq (g₁.form x) v)
    (q : M.Carrier) (hq : inducedDistance g₁.form p q ≤ 1) :
    inducedDistance g₀.form p q < 2 := by
  let := manifold_realSmooth M
  let := manifold_realPhase M
  let : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g₀.form x
  obtain ⟨v, hv, hvnorm⟩ := exists_minimizing_realExponential g₁ p q
  let P : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨p, v⟩
  let γ := realGeodesicFlow g₁ P
  let β := fun s => (γ s).proj
  have hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ β :=
    (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).comp (realGeodesicFlow_contMDiff g₁ P)
  have hβ0 : β 0 = p := congrArg Bundle.TotalSpace.proj (realGeodesicFlow_zero g₁ P)
  have hβ1 : β 1 = q := hv
  have hVelocity (s : ℝ) : realCurveVelocity β s = (γ s).2 :=
    realCurveVelocity_realGeodesic g₁ γ ((realGeodesicFlow_integral g₁ P).isMIntegralCurveAt s)
  have hSpeed₁ (s : ℝ) :
      @norm _ (underlyingRealTangentNormedAddCommGroup g₁.form (β s)).toNorm (γ s).2 ≤ 1 := by
    exact (realGeodesicFlow_velocity_norm g₁ P s).trans_le (hvnorm.trans_le hq)
  have hcont : Continuous (fun s => inducedDistance g₀.form p (β s)) :=
    (L23Aux.continuous_distFrom g₀.form (metricSmooth_of_smoothMetric g₀) p).comp hβ.continuous
  have hAll : ∀ s ∈ Icc (0 : ℝ) 1, inducedDistance g₀.form p (β s) < 2 := by
    apply first_exit_barrier hcont (by rw [hβ0, g₀.induced_distance_eq_zero.mpr rfl]; norm_num)
    intro s hs hPrevious
    have hSpeed₀ : ∀ u ∈ Icc (0 : ℝ) s, ‖realCurveVelocity β u‖ ≤ (3 / 2 : ℝ) := by
      intro u hu
      rw [hVelocity u]
      have hN := realTangentNorm_le_of_quadratic_comparison g₀.form g₁.form (β u)
        (3 / 2) (by norm_num) (hCompare (β u) (hPrevious u hu)) (γ u).2
      exact hN.trans (by have hh := hSpeed₁ u; nlinarith)
    have hD := inducedDistance_le_of_path_speed_bound g₀ β s (3 / 2) hs.1
      (by norm_num) hβ hSpeed₀
    rw [hβ0] at hD
    linarith [hs.2]
  simpa only [hβ1] using hAll 1 (by constructor <;> norm_num)

end Yau.Blueprint.C02Proof
