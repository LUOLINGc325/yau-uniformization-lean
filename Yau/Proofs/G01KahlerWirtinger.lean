import Yau.Proofs.G01KahlerClosure
import Yau.LeafProofs.L17ChartNaturality
import Yau.LeafProofs.L14

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs L14Aux

theorem kahler_hMat_wirtBar_symm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) (i j k : Fin n) :
    wirtBar (fun y => hMat h a y j k) z (stdVec i) =
      wirtBar (fun y => hMat h a y i k) z (stdVec j) := by
  let G := hMat h a
  let R := fun p q d => rDeriv (fun y => (G y p q).re) z d
  let I := fun p q d => rDeriv (fun y => (G y p q).im) z d
  have hDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => G y p q) z :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs a p q).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  have hRDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => (G y p q).re) z :=
    Complex.reCLM.differentiableAt.comp z (hDiff p q)
  have hIDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => (G y p q).im) z :=
    Complex.imCLM.differentiableAt.comp z (hDiff p q)
  have hRe (p q : Fin n) : (fun y => (G y p q).re) = fun y => (G y q p).re := by
    funext y
    have he := congrArg Complex.re ((L12Aux.hMat_isHermitian h a y).apply p q)
    simpa only [Complex.star_def, Complex.conj_re] using he.symm
  have hIm (p q : Fin n) : (fun y => (G y p q).im) = fun y => -(G y q p).im := by
    funext y
    have he := congrArg Complex.im ((L12Aux.hMat_isHermitian h a y).apply p q)
    simpa only [Complex.star_def, Complex.conj_im] using he.symm
  have hRsym (p q : Fin n) (d : RIdx n) : R p q d = R q p d :=
    congrArg (fun f : ComplexVector n → ℝ => rDeriv f z d) (hRe p q)
  have hNeg (f : ComplexVector n → ℝ) (d : RIdx n) :
      rDeriv (fun y => -f y) z d = -rDeriv f z d := by
    unfold rDeriv
    rw [fderiv_fun_neg]
    rfl
  have hIskew (p q : Fin n) (d : RIdx n) : I p q d = -I q p d := by
    change rDeriv (fun y => (G y p q).im) z d = -rDeriv (fun y => (G y q p).im) z d
    rw [hIm p q, hNeg]
  have hScaleR (p q : Fin n) (c : ℝ) (d : RIdx n) :
      rDeriv (fun y => c * (hMat h a y p q).re) z d = c * R p q d :=
    L12Aux.rDeriv_const_mul (hRDiff p q) c d
  have hScaleI (p q : Fin n) (c : ℝ) (d : RIdx n) :
      rDeriv (fun y => c * (hMat h a y p q).im) z d = c * I p q d :=
    L12Aux.rDeriv_const_mul (hIDiff p q) c d
  have C1 := kahlerClosed_in_chart h hs hk a hz (i, 0) (j, 0) (k, 1)
  have C2 := kahlerClosed_in_chart h hs hk a hz (i, 1) (j, 1) (k, 1)
  have C3 := kahlerClosed_in_chart h hs hk a hz (i, 0) (j, 0) (k, 0)
  have C4 := kahlerClosed_in_chart h hs hk a hz (i, 1) (j, 1) (k, 0)
  norm_num only [L12Aux.kahlerFormFn_entries, Prod.fst, Prod.snd, Fin.reduceEq,
    ite_true, ite_false, mul_neg] at C1 C2 C3 C4
  simp only [hNeg, hScaleR, hScaleI] at C1 C2 C3 C4
  have hfirst := wirtBar_real_components (fun y => G y j k) z (hDiff j k) i
  have hsecond := wirtBar_real_components (fun y => G y i k) z (hDiff i k) j
  apply Complex.ext
  · rw [hfirst.1, hsecond.1]
    change (1 / 2 : ℝ) * (R j k (i, 0) - I j k (i, 1)) =
      (1 / 2 : ℝ) * (R i k (j, 0) - I i k (j, 1))
    nlinarith [hRsym k i (j, 0), hIskew k i (j, 1)]
  · rw [hfirst.2, hsecond.2]
    change (1 / 2 : ℝ) * (I j k (i, 0) + R j k (i, 1)) =
      (1 / 2 : ℝ) * (I i k (j, 0) + R i k (j, 1))
    nlinarith [hIskew k i (j, 0), hRsym k i (j, 1)]


/-- Conjugation transfers the anti-holomorphic Kähler symmetry to holomorphic indices. -/
theorem kahler_hMat_wirt_symm {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a) (i j k : Fin n) :
    wirt (fun y => hMat h a y k j) z (stdVec i) =
      wirt (fun y => hMat h a y k i) z (stdVec j) := by
  have he := congrArg star (kahler_hMat_wirtBar_symm h hs hk a z hz i j k)
  have hc (p q : Fin n) : (fun y => hMat h a y q p) =
      (fun y => star (hMat h a y p q)) := by
    funext y
    exact (L12Aux.hMat_isHermitian h a y).apply q p |>.symm
  rw [hc j k, hc i k, L14Aux.wirt_star, L14Aux.wirt_star]
  exact he

end Yau.NodeProofs.G01Aux
