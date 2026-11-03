import Yau.LeafProofs.L17LocalizedSchauderRawHolder

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- A genuinely local supported scalar family gives a global Y element,
using only N and 2N active terms. This also applies to residuals whose
cutoff has already been included. -/
theorem exists_uniform_raw_sum_holder (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (gamma : ℝ) (hγ : 0 ≤ gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : UniformChartPartition g), P.charts = A → P.overlapBudget ≤ N →
      ∀ (hρone : P.radius ≤ 1), 2*P.radius < A.radius → ∀ (T a b : ℝ), 0 ≤ a → 0 ≤ b →
      ∀ (v : P.centers → ComplexVector n × Time T → ℝ),
      (∀ p, ContinuousOn (v p) (ball (0 : ComplexVector n) (2*P.radius) ×ˢ Set.univ)) →
      (∀ p z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v p (z,t) = 0) →
      (∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → ∀ t, |v p (z,t)| ≤ a) →
      (∀ p z w, z ∈ ball (0 : ComplexVector n) (2*P.radius) → w ∈ ball 0 (2*P.radius) →
        ∀ t s : Time T, |v p (z,t)-v p (w,s)| ≤ b*(localScaledDistance P.radius (z,t) (w,s))^gamma) →
      ∃! u : HolderSpace P T gamma,
        holderFun u = (fun q => ∑ᶠ p, rawLocalizedTerm P T p (v p) q) ∧ ‖u‖ ≤ C*(a+b) := by
  obtain ⟨K,hK,hRaw⟩ := exists_uniform_raw_transport_holder_budget A hg gamma hγ
  let C := 1+max (N : ℝ) (2*(N : ℝ)*K)
  have hC : 0 < C := by
    dsimp only [C]
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith [le_max_left (N : ℝ) (2*(N : ℝ)*K)]
  refine ⟨C,hC,?_⟩
  intro P hPA hPN hρone hρr T a b ha hb v hv hZero hSup hHolder
  have hAB : 0 ≤ a+b := add_nonneg ha hb
  have hKB : 0 ≤ K*(a+b) := mul_nonneg hK.le hAB
  have hWeighted (p : P.centers) (i : ChartPairs P T) :
      |pairWeight P T gamma i*(rawLocalizedTerm P T p (v p) (chartRight P T i)-
        rawLocalizedTerm P T p (v p) (chartLeft P T i))| ≤ K*(a+b) :=
    (hRaw P hPA hρone hρr T a b ha hb p (v p) (hZero p) (hSup p) (hHolder p)).2 i
  let u := supportedSumHolder P T gamma (fun p => rawLocalizedTerm P T p (v p))
    (fun p => rawLocalizedTerm_continuous P T p (v p) (hv p) (hZero p))
    (fun p q hq => rawLocalizedTerm_zero_of_not_cover P T p (v p) q hq)
    a (K*(a+b)) ha hKB (fun p => rawLocalizedTerm_abs_le P T p (v p) ha (hSup p)) hWeighted
  have hNorm : ‖u‖ ≤ C*(a+b) := by
    apply (supportedSumHolder_norm_le _ _ _ _ _ _ _ _ _ _ _ _).trans
    apply max_le
    · have hNC : (N : ℝ) ≤ C := by dsimp only [C]; linarith [le_max_left (N : ℝ) (2*(N : ℝ)*K)]
      exact mul_le_mul ((show (P.overlapBudget : ℝ) ≤ N by exact_mod_cast hPN).trans hNC)
        (le_add_of_nonneg_right hb) ha hC.le
    · have hNC : 2*(N : ℝ)*K ≤ C := by dsimp only [C]; linarith [le_max_right (N : ℝ) (2*(N : ℝ)*K)]
      have hCoef : 2*(P.overlapBudget : ℝ)*K ≤ 2*(N : ℝ)*K := by
        apply mul_le_mul_of_nonneg_right _ hK.le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hPN) (by norm_num)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hCoef.trans hNC) hAB
  refine ⟨u,⟨rfl,hNorm⟩,?_⟩
  intro u' hu'
  exact holderFun_injective P T gamma hu'.1

end Yau.LeafProofs.L17LocalizedSchauderAux
