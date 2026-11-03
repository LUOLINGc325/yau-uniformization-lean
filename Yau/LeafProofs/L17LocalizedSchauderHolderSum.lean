import Yau.LeafProofs.L17LocalizedSchauderOverlap

open Set Metric Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem weighted_supported_finsum_difference_le (P : UniformChartPartition g) (T gamma : ℝ)
    (f : P.centers → Cylinder M T → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (hB : ∀ p (i : ChartPairs P T),
      |pairWeight P T gamma i*(f p (chartRight P T i)-f p (chartLeft P T i))| ≤ B)
    (i : ChartPairs P T) :
    |pairWeight P T gamma i*((∑ᶠ p, f p (chartRight P T i))-(∑ᶠ p, f p (chartLeft P T i)))| ≤
      (2*(P.overlapBudget : ℝ))*B := by
  classical
  obtain ⟨I,hI,hRight⟩ := exists_active_finset P (chartRight P T i).1
  obtain ⟨J,hJ,hLeft⟩ := exists_active_finset P (chartLeft P T i).1
  have hh := norm_smul_finsum_sub_le_two_overlap
    (fun p => f p (chartRight P T i)) (fun p => f p (chartLeft P T i))
    I J P.overlapBudget (pairWeight P T gamma i) B hB0 hI hJ
    (fun p hp => hSupp p _ (hRight p hp)) (fun p hp => hSupp p _ (hLeft p hp))
    (fun p _ => by simpa only [Real.norm_eq_abs,smul_eq_mul] using hB p i)
  simpa only [Real.norm_eq_abs,smul_eq_mul] using hh

/-- Genuine local scalar bounds and actual support localization suffice
for a global Holder element. The two-point budget is exactly 2N. -/
def supportedSumHolder (P : UniformChartPartition g) (T gamma : ℝ)
    (f : P.centers → Cylinder M T → ℝ) (hf : ∀ p, Continuous (f p))
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ p q, |f p q| ≤ A)
    (hB : ∀ p (i : ChartPairs P T),
      |pairWeight P T gamma i*(f p (chartRight P T i)-f p (chartLeft P T i))| ≤ B) :
    HolderSpace P T gamma :=
  ofBounds P T gamma (fun q => ∑ᶠ p, f p q) (continuous_supported_finsum P T f hf hSupp)
    ((P.overlapBudget : ℝ)*A) ((2*(P.overlapBudget : ℝ))*B)
    (fun q => by
      have hh := norm_supported_finsum_le P T f A hA0 hSupp
        (fun p q => by simpa only [Real.norm_eq_abs] using hA p q) q
      simpa only [Real.norm_eq_abs] using hh)
    (weighted_supported_finsum_difference_le P T gamma f B hB0 hSupp hB)

theorem supportedSumHolder_value (P : UniformChartPartition g) (T gamma : ℝ)
    (f : P.centers → Cylinder M T → ℝ) (hf : ∀ p, Continuous (f p))
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ p q, |f p q| ≤ A)
    (hB : ∀ p (i : ChartPairs P T),
      |pairWeight P T gamma i*(f p (chartRight P T i)-f p (chartLeft P T i))| ≤ B) :
    holderFun (supportedSumHolder P T gamma f hf hSupp A B hA0 hB0 hA hB) =
      (fun q => ∑ᶠ p, f p q) := rfl

theorem supportedSumHolder_norm_le (P : UniformChartPartition g) (T gamma : ℝ)
    (f : P.centers → Cylinder M T → ℝ) (hf : ∀ p, Continuous (f p))
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ p q, |f p q| ≤ A)
    (hB : ∀ p (i : ChartPairs P T),
      |pairWeight P T gamma i*(f p (chartRight P T i)-f p (chartLeft P T i))| ≤ B) :
    ‖supportedSumHolder P T gamma f hf hSupp A B hA0 hB0 hA hB‖ ≤
      max ((P.overlapBudget : ℝ)*A) ((2*(P.overlapBudget : ℝ))*B) := by
  apply ofBounds_norm_le <;> positivity

theorem supported_finsum_add (P : UniformChartPartition g) (T : ℝ)
    {F : Type*} [NormedAddCommGroup F] (f h : P.centers → Cylinder M T → F)
    (hf : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (hh : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → h p q = 0)
    (q : Cylinder M T) :
    (∑ᶠ p, (f p q+h p q)) = (∑ᶠ p, f p q)+(∑ᶠ p, h p q) := by
  classical
  obtain ⟨I,hI,hActive⟩ := exists_active_finset P q.1
  have hF := finsum_eq_sum_of_support_subset (fun p => f p q)
    (s := I) (fun p hp => by by_contra hn; exact hp (hf p q (hActive p hn)))
  have hH := finsum_eq_sum_of_support_subset (fun p => h p q)
    (s := I) (fun p hp => by by_contra hn; exact hp (hh p q (hActive p hn)))
  have hSum := finsum_eq_sum_of_support_subset (fun p => f p q+h p q)
    (s := I) (fun p hp => by
      by_contra hn
      exact hp (by
        change f p q+h p q = 0
        rw [hf p q (hActive p hn),hh p q (hActive p hn),add_zero]))
  rw [hF,hH,hSum,Finset.sum_add_distrib]

theorem supported_finsum_smul (P : UniformChartPartition g) (T : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P.centers → Cylinder M T → F) (c : ℝ)
    (hf : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (q : Cylinder M T) : (∑ᶠ p, c • f p q) = c • (∑ᶠ p, f p q) := by
  classical
  obtain ⟨I,hI,hActive⟩ := exists_active_finset P q.1
  have hF := finsum_eq_sum_of_support_subset (fun p => f p q)
    (s := I) (fun p hp => by by_contra hn; exact hp (hf p q (hActive p hn)))
  have hC := finsum_eq_sum_of_support_subset (fun p => c • f p q)
    (s := I) (fun p hp => by
      by_contra hn
      exact hp (by change c • f p q = 0; rw [hf p q (hActive p hn),smul_zero]))
  rw [hF,hC,Finset.smul_sum]

end Yau.LeafProofs.L17LocalizedSchauderAux
