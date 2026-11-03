import Yau.Proofs.C02MetricSlice
import Yau.Proofs.G01RicciNormalization

/-! The supplied complex flow has the actual real physical clock sigma=1.
The one-sided initial derivative is retained. No complete slice is used here. -/

noncomputable section
open Set
open scoped ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem localRealRicciFlow_of_kahlerRicciFlow
    (g : HermitianField M) (h : ℝ → HermitianField M)
    (hflow : IsKahlerRicciFlow g h) : LocalRealRicciFlow h univ (Ici 0) 1 := by
  refine ⟨hflow.2.1, ?_⟩
  intro x _ t ht a b
  have hs := metricFamilySmooth_slice hflow.2.1 ht
  have hk := hflow.2.2.1 t ht
  have hRic : realRicciCoeff (h t) x (chartPt x x) a b =
      2 * rawReal (ricci (h t) x) a b := by
    rw [L23Aux.realRicciCoeff_eq_realRicciMatrix (h t) x (chartPt x x) (mem_extChartAt_target x),
      realRicciMatrix_eq_realification (h t) hs hk x (chartPt x x) (mem_extChartAt_target x),
      hermitianRealification_eq]
    rfl
  rw [hRic]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  have hd := hflow.2.2.2 x t ht i j
  have hre : HasDerivWithinAt (fun s => (gMat (h s) x i j).re)
      (-(ricci (h t) x i j).re) (Ici 0) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.neg_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have him : HasDerivWithinAt (fun s => (gMat (h s) x i j).im)
      (-(ricci (h t) x i j).im) (Ici 0) t := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.neg_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  fin_cases a <;> fin_cases b
  · simpa [L12Aux.realMetricFn_entries, gMat, rawReal, mul_neg] using hre.const_mul 2
  · simpa [L12Aux.realMetricFn_entries, gMat, rawReal, mul_neg, Pi.neg_apply] using him.neg.const_mul 2
  · simpa [L12Aux.realMetricFn_entries, gMat, rawReal, mul_neg] using him.const_mul 2
  · simpa [L12Aux.realMetricFn_entries, gMat, rawReal, mul_neg] using hre.const_mul 2

theorem localRealRicciFlow_on_slab
    (g : HermitianField M) (h : ℝ → HermitianField M)
    (hflow : IsKahlerRicciFlow g h) (O : Set M.Carrier) (a b : ℝ) (ha : 0 ≤ a) :
    LocalRealRicciFlow h O (Icc a b) 1 := by
  have hh := localRealRicciFlow_of_kahlerRicciFlow g h hflow
  have hI : Icc a b ⊆ Ici 0 := fun t ht => ha.trans ht.1
  refine ⟨fun x i j => (hh.1 x i j).mono (prod_mono Subset.rfl hI), ?_⟩
  intro x _ t ht i j
  exact (hh.2 x (mem_univ x) t (hI ht) i j).mono hI

end Yau.Blueprint.C02Proof
