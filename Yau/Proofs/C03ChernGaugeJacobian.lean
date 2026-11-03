import Yau.Proofs.C03ChernGaugeFlat

/-! The gauge is the Jacobian of the actual holomorphic coordinate map;
its matrix congruence is proved from the given intrinsic pullback equality. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs L12Aux L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem coordinate_open
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Φ : ComplexVector n → M.Carrier} (hΦ : ContinuousOn Φ O) (c : M.Carrier) :
    IsOpen (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) :=
  hΦ.isOpen_inter_preimage hO (isOpen_extChartAt_source c)

theorem coordinate_holomorphic
    {O : Set (ComplexVector n)} {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O) (c : M.Carrier) :
    ContDiffOn ℂ ∞ (fun w => chartPt c (Φ w))
      (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) := by
  simpa only [chartPt, extChartAt_source, Function.comp_def] using
    ((contMDiffOn_extChartAt (I := ComplexModel n) (x := c) (n := ∞)).comp
      (hΦ.mono Set.inter_subset_left) (fun _ hz => hz.2)).contDiffOn

theorem coordinateDifferential_eq_fderiv
    (Φ : ComplexVector n → M.Carrier) (c : M.Carrier) (z : ComplexVector n)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source) :
    coordinateDifferential Φ c z = fderiv ℂ (fun w => chartPt c (Φ w)) z := by
  apply ContinuousLinearMap.ext
  intro u
  rw [coordinateDifferential_apply]
  have H := congrArg (fun L => L u)
    (mfderiv_comp (I := ComplexModel n) (I' := ComplexModel n) (I'' := ComplexModel n)
      z (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)) hΦ)
  rw [mfderiv_eq_fderiv] at H
  exact H.symm

theorem jacobian_holomorphic
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {f : ComplexVector n → ComplexVector n} (hf : ContDiffOn ℂ ∞ f O) (i j : Fin n) :
    ContDiffOn ℂ ∞ (fun w => linearMatrix (fderiv ℂ f w) i j) O := by
  have hd := hf.fderiv_of_isOpen hO (m := ∞) (by simp)
  exact (contDiffOn_piLp 2).mp (hd.clm_apply contDiffOn_const) i

theorem jacobian_injective
    (Φ : ComplexVector n → M.Carrier) (c : M.Carrier) (z : ComplexVector n)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source)
    (hbij : Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z)) :
    Function.Injective (fderiv ℂ (fun w => chartPt c (Φ w)) z) := by
  rw [← coordinateDifferential_eq_fderiv Φ c z hΦ hy]
  intro u v huv
  apply hbij.injective
  have H := congrArg (chartVec c (Φ z)) huv
  simpa only [coordinateDifferential_apply, chartVec_tangentCoords c (Φ z) hy] using H

theorem source_gMat_congruence
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (h : HermitianField M) (Φ : ComplexVector n → M.Carrier)
    (z : (ComplexEuclideanManifold n hn).Carrier) (c : M.Carrier)
    (hΦ : MDifferentiableAt (ComplexModel n) (ComplexModel n) Φ z)
    (hy : Φ z ∈ (extChartAt (ComplexModel n) c).source)
    (heq : ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v)) :
    gMat k z = (linearMatrix (fderiv ℂ (fun w => chartPt c (Φ w)) z))ᴴ *
      hMat h c (chartPt c (Φ z)) * linearMatrix (fderiv ℂ (fun w => chartPt c (Φ w)) z) := by
  have H : gMat k z = pullbackMatrix h Φ z := by
    ext i j
    change hMat k z (chartPt z z) i j = _
    rw [flat_chartPt hn, flat_hMat_apply hn]
    exact heq (stdVec i) (stdVec j)
  rw [H, pullbackMatrix_eq_congruence h Φ c z hy,
    coordinateDifferential_eq_fderiv Φ c z hΦ hy]

end Yau.Proofs.C03Aux.ChernGauge
