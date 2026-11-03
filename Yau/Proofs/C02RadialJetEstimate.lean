import Yau.Proofs.C02RadialHomotopy
import Yau.Proofs.C02RadialIntegrandJets
import Yau.Proofs.C02ParametricJets

/-! The all-order radial homotopy estimate with its exact two gains. The
highest jet has coefficient rho/(m+2), and the lower jet coefficient m/(m+1). -/

noncomputable section
open Set
open scoped Interval ContDiff
universe u
namespace Yau.Blueprint.C02Proof
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_iteratedFDeriv_radialHomotopy_le
    (T : E → E →L[ℝ] F) (hT : ContDiff ℝ ∞ T)
    (k : ℕ) (x : E) (ρ a b : ℝ) (hx : ‖x‖ ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hTop : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (k + 1) T (t • x)‖ ≤ a)
    (hLow : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k T (t • x)‖ ≤ b) :
    ‖iteratedFDeriv ℝ (k + 1) (radialHomotopy T) x‖ ≤
      ρ / ((k : ℝ) + 3) * a + ((k : ℝ) + 1) / ((k : ℝ) + 2) * b := by
  have hG : ContDiff ℝ ∞ (fun p : E × ℝ => p.2 • (T (p.2 • p.1) p.1)) :=
    contDiff_snd.smul ((hT.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst)
  have hInt : iteratedFDeriv ℝ (k + 1) (radialHomotopy T) x =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ (k + 1) (fun y => t • (T (t • y) y)) x :=
    iteratedFDeriv_intervalIntegral_smooth _ hG (k + 1) x
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) (fun y => t • (T (t • y) y)) x‖ ≤
        (ρ * a) * t ^ ((k + 1) + 1) + ((k + 1 : ℕ) : ℝ) * b * t ^ (k + 1) := by
    intro t ht
    have htop := mul_le_mul_of_nonneg_left (hTop t ht) (pow_nonneg ht.1 (k + 2))
    have htop' := mul_le_mul htop hx (norm_nonneg x)
      (mul_nonneg (pow_nonneg ht.1 (k + 2)) ha)
    have hlow := mul_le_mul_of_nonneg_left (hLow t ht)
      (mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) (pow_nonneg ht.1 (k + 1)))
    calc
      _ ≤ t ^ (k + 2) * ‖iteratedFDeriv ℝ (k + 1) T (t • x)‖ * ‖x‖ +
          ((k : ℝ) + 1) * t ^ (k + 1) * ‖iteratedFDeriv ℝ k T (t • x)‖ :=
        norm_iteratedFDeriv_radial_integrand_le T hT k x t ht.1
      _ ≤ t ^ (k + 2) * a * ρ + ((k : ℝ) + 1) * t ^ (k + 1) * b :=
        add_le_add htop' hlow
      _ = _ := by push_cast; ring
  rw [hInt]
  have hi := norm_integral_radial_weights (k + 1)
    (fun t => iteratedFDeriv ℝ (k + 1) (fun y => t • (T (t • y) y)) x) (ρ * a) b hbound
  convert hi using 1 <;> push_cast <;> ring

end Yau.Blueprint.C02Proof
