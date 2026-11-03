import Yau.Proofs.V03LeviLinear
import Yau.Proofs.V04PhysicalTime
import Yau.Proofs.V04DualNormOrder

/-! Linearity of the original heat operator is taken within its actual
time slab. Spatial derivatives use the genuine centered chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace Yau.Blueprint.V04Proof.HeatAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_slice {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) {t : ℝ} (ht : t ∈ I) : SmoothFn (fun x => u x t) := by
  intro x
  exact (hu x).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz, ht⟩)

theorem smoothSpaceTime_time_contDiffOn {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) (x : M.Carrier) : ContDiffOn ℝ ∞ (u x) I := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hh := (hu x).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun t ht => ⟨(extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x), ht⟩)
  change ContDiffOn ℝ ∞ (fun τ => u (chartInv x (chartPt x x)) τ) I at hh
  simpa only [hx] using hh

theorem laplacian_add_at (h : HermitianField M) {f g : M.Carrier → ℝ}
    (x : M.Carrier) (hf : ContDiffAt ℝ 2 (inChart x f) (chartPt x x))
    (hg : ContDiffAt ℝ 2 (inChart x g) (chartPt x x)) :
    laplacian h (fun y => f y + g y) x = laplacian h f x + laplacian h g x := by
  have heq := congrArg (traceWith (gMat h x)) (leviMatrix_add hf hg stdVec)
  change traceWith (gMat h x) (leviMatrix (fun z => inChart x f z + inChart x g z)
    (chartPt x x) stdVec) = traceWith (gMat h x) (leviMatrix (inChart x f) (chartPt x x) stdVec) +
      traceWith (gMat h x) (leviMatrix (inChart x g) (chartPt x x) stdVec)
  simpa only [traceWith, Matrix.mul_add, Matrix.trace_add, Complex.add_re] using heq

theorem laplacian_const_mul_at (h : HermitianField M) {f : M.Carrier → ℝ}
    (x : M.Carrier) (hf : ContDiffAt ℝ 2 (inChart x f) (chartPt x x)) (c : ℝ) :
    laplacian h (fun y => c * f y) x = c * laplacian h f x := by
  have heq := congrArg (traceWith (gMat h x)) (leviMatrix_const_mul hf c stdVec)
  change traceWith (gMat h x) (leviMatrix (fun z => c * inChart x f z)
    (chartPt x x) stdVec) = c * traceWith (gMat h x) (leviMatrix (inChart x f) (chartPt x x) stdVec)
  simpa only [traceWith, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using heq

theorem laplacian_add (h : HermitianField M) {f g : M.Carrier → ℝ}
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    laplacian h (fun y => f y + g y) x = laplacian h f x + laplacian h g x := by
  have hz := (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hopen := isOpen_extChartAt_target (I := ComplexModel n) x
  exact laplacian_add_at h x (((hf x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp))
    (((hg x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp))

theorem laplacian_const_mul (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun y => c * f y) x = c * laplacian h f x := by
  have hz := (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hopen := isOpen_extChartAt_target (I := ComplexModel n) x
  exact laplacian_const_mul_at h x (((hf x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp)) c

theorem heatOp_linear_combination {q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} {u v : X.manifold.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) (hv : SmoothSpaceTime v I) (c : ℝ)
    (x : X.manifold.Carrier) {t : ℝ} (ht : t ∈ I) :
    heatOp d.h I (fun y τ => c * u y τ + v y τ) x t =
      c * heatOp d.h I u x t + heatOp d.h I v x t := by
  have hdu := ((smoothSpaceTime_time_contDiffOn hu x).differentiableOn (by simp)) t ht
  have hdv := ((smoothSpaceTime_time_contDiffOn hv x).differentiableOn (by simp)) t ht
  unfold heatOp
  change derivWithin ((fun τ => c * u x τ) + v x) I t -
    laplacian (d.h t) (fun y => c * u y t + v y t) x = _
  rw [derivWithin_add (hdu.const_mul c) hdv, derivWithin_const_mul c hdu,
    laplacian_add (d.h t) (fun z => contDiffOn_const.mul (smoothSpaceTime_slice hu ht z))
      (smoothSpaceTime_slice hv ht), laplacian_const_mul _ (smoothSpaceTime_slice hu ht)]
  ring

theorem traceWith_metric_nonneg (h g : HermitianField M) (x : M.Carrier) :
    0 ≤ traceWith (gMat h x) (gMat g x) := by
  let A := (gMat h x)⁻¹
  let S := CFC.sqrt A
  have hA : A.PosSemidef := (gMat_posDef h x).inv.posSemidef
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp : (S * gMat g x * S).PosSemidef := by
    simpa only [hS.eq] using (gMat_posDef g x).posSemidef.conjTranspose_mul_mul_same S
  have heq : Matrix.trace (S * gMat g x * S) = Matrix.trace (A * gMat g x) := by
    rw [Matrix.trace_mul_cycle, hSS]
  exact (Complex.nonneg_iff.mp (heq ▸ hp.trace_nonneg)).1

theorem baseCost_heatOp_nonneg {q : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) (x : X.manifold.Carrier) {t : ℝ}
    (ht : t ∈ Set.Icc 0 d.T) :
    0 ≤ heatOp d.h (Set.Icc 0 d.extendedT) (baseCost d j) x t := by
  have ht' : t ∈ Set.Icc 0 d.extendedT := ⟨ht.1, ht.2.trans hd.2.1.le⟩
  have hQ := hd.2.2.2.2.2.2.2.2.1
  have hρ := hd.2.2.2.2.2.2.2.2.2.1 j
  obtain ⟨c, hc, hQbound⟩ := hQ.2
  obtain ⟨C, hρbound⟩ := hρ.2
  have hQheat : 0 ≤ heatOp d.h (Set.Icc 0 d.extendedT) d.Q x t :=
    (mul_nonneg hc.le (traceWith_metric_nonneg (d.h t) X.metric.form x)).trans
      (hQbound x t ht').2
  have hρheat := (hρbound x t ht').2.2.2
  change 0 ≤ heatOp d.h (Set.Icc 0 d.extendedT)
    (fun y τ => ((j + 1 : ℕ) : ℝ)⁻¹ * d.Q y τ + d.rhoTail j y τ) x t
  rw [heatOp_linear_combination (d := d) hQ.1 hρ.1 _ x ht']
  exact add_nonneg (mul_nonneg (by positivity) hQheat) hρheat

theorem baseCost_laplacian_le_timeDerivative {q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) (x : X.manifold.Carrier)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) :
    laplacian (d.h t) (fun y => baseCost d j y t) x ≤
      derivWithin (baseCost d j x) (Set.Ici 0) t := by
  have hh := baseCost_heatOp_nonneg hd j x ht
  unfold heatOp at hh
  rw [physicalTime_derivWithin_extended_interval _ ht hd.2.1] at hh
  linarith only [hh]

end Yau.Blueprint.V04Proof.HeatAux
