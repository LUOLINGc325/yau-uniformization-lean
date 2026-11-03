import Yau.LeafProofs.L19HeatRegularity
import Yau.LeafProofs.L19HeatGaussianTailPointwise

/-! The actual classical heat representative, with derived positivity and Gaussian comparison. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- A fixed choice of the internally constructed actual classical heat. -/
def scalarClassicalHeat (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    M.Carrier → ℝ → ℝ :=
  Classical.choose (scalarHeat_exists_classicalRepresentative hn g hK μ hμ f)

theorem scalarClassicalHeat_smooth (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    SmoothSpaceTime (scalarClassicalHeat hn g hK μ hμ f) (Ioi 0) :=
  (Classical.choose_spec (scalarHeat_exists_classicalRepresentative hn g hK μ hμ f)).1

theorem scalarClassicalHeat_ae (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    (fun x => scalarClassicalHeat hn g hK μ hμ f x t) =ᵐ[μ] scalarHeatFamily g μ hμ t f :=
  (Classical.choose_spec (scalarHeat_exists_classicalRepresentative hn g hK μ hμ f)).2.1 t ht

theorem scalarClassicalHeat_pde (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    deriv (scalarClassicalHeat hn g hK μ hμ f x) t =
      laplacian g.form (fun y => scalarClassicalHeat hn g hK μ hμ f y t) x :=
  (Classical.choose_spec (scalarHeat_exists_classicalRepresentative hn g hK μ hμ f)).2.2 x t ht

theorem scalarClassicalHeat_hasDerivAt (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarClassicalHeat hn g hK μ hμ f x)
      (laplacian g.form (fun y => scalarClassicalHeat hn g hK μ hμ f y t) x) t := by
  have hd := (smoothSpaceTime_time_contDiffAt (scalarClassicalHeat_smooth hn g hK μ hμ f) x
    (Ioi_mem_nhds ht)).differentiableAt (by simp)
  rw [← scalarClassicalHeat_pde hn g hK μ hμ f x ht]
  exact hd.hasDerivAt

theorem scalarClassicalHeat_nonneg (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    0 ≤ scalarClassicalHeat hn g hK μ hμ f x t :=
  scalarHeatRepresentative_nonneg g μ hμ f hf (scalarClassicalHeat_smooth hn g hK μ hμ f)
    (fun _t ht => (scalarClassicalHeat_ae hn g hK μ hμ f ht).symm) x t ht

/-- Gaussian lower comparison is now a theorem of the actual constructed
heat, with every intermediate representative and uniform initial trace closed. -/
theorem scalarClassicalGaussianHeat_lower (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a : ℝ} (ha : 0 < a)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    Real.exp (-((2 * n : ℕ) * a * t)) * gaussianWeight g o a x ≤
      scalarClassicalHeat hn g hK μ hμ (scalarGaussianL2 g hK hRic μ hμ o a ha) x t := by
  let f := scalarGaussianL2 g hK hRic μ hμ o a ha
  have hf : ∀ᵐ y ∂μ, 0 ≤ f y := by
    filter_upwards [scalarGaussianL2_coe g hK hRic μ hμ o a ha] with y hy
    rw [hy]
    exact (Real.exp_pos _).le
  apply gaussianWeight_heat_comparison_sharp g hK hRic o ha
    (scalarClassicalHeat_smooth hn g hK μ hμ f)
    (fun y τ hτ => scalarClassicalHeat_nonneg hn g hK μ hμ f hf y hτ)
    (fun y τ hτ => scalarClassicalHeat_hasDerivAt hn g hK μ hμ f y hτ)
  · exact scalarHeat_gaussian_uniform_initial g hK hRic μ hμ o ha
      (fun τ hτ => continuous_of_smoothFn
        (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ f) hτ))
      (fun τ hτ => scalarClassicalHeat_ae hn g hK μ hμ f hτ)
  · exact ht

/-- Gaussian spatial decay of the actual classical Gaussian heat,
uniformly on every compact positive time slab. -/
theorem scalarClassicalGaussianHeat_tail (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {a : ℝ} (ha : 0 < a) {l b : ℝ} (hl : 0 < l) (hlb : l ≤ b) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ x t, t ∈ Icc l b →
      |scalarClassicalHeat hn g hK μ hμ (scalarGaussianL2 g hK hRic μ hμ o a ha) x t| ≤
        C * Real.exp (-β * inducedDistance g.form o x ^ 2) := by
  let f := scalarGaussianL2 g hK hRic μ hμ o a ha
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarGaussianHeatRepresentative_gaussian_tail g hcomplete hK hRic μ hμ o a ha
    (scalarClassicalHeat_smooth hn g hK μ hμ f)
    (fun x t ht => scalarClassicalHeat_pde hn g hK μ hμ f x ht)
    (fun t ht => (scalarClassicalHeat_ae hn g hK μ hμ f ht).symm) l b hl hlb
  refine ⟨C, β, hC, hβ, ?_⟩
  intro x t ht
  have hlow := scalarClassicalGaussianHeat_lower hn g hK hRic μ hμ o ha x (hl.trans_le ht.1)
  have hnonneg : 0 ≤ Real.exp (-((2 * n : ℕ) * a * t)) * gaussianWeight g o a x :=
    mul_nonneg (Real.exp_pos _).le (gaussianWeight_pos g o a x).le
  rw [abs_of_nonneg (hnonneg.trans hlow)]
  exact htail x t ht

end Yau.LeafProofs.L19Aux
