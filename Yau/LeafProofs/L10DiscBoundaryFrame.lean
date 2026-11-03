import Yau.LeafProofs.L10DiscAngularBootstrap

/-! The radial Euler field and the exact real linear frame on the
punctured disc. Interior identities use actual Fréchet derivatives. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discBoundaryEuler (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderivWithin ℝ g (Metric.closedBall (0 : ℂ) 1) z z

def discBoundaryFrame (z a b : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight ((Complex.normSq z)⁻¹ • (z.re • a - z.im • b)) +
  Complex.imCLM.smulRight ((Complex.normSq z)⁻¹ • (z.im • a + z.re • b))

theorem discBoundary_real_coordinates (z : ℂ) :
    z = z.re • (1 : ℂ) + z.im • Complex.I := by
  apply Complex.ext <;> simp

theorem discBoundary_linear_coordinates (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = z.re • L 1 + z.im • L Complex.I := by
  conv_lhs => rw [discBoundary_real_coordinates z]
  rw [map_add, map_smul, map_smul]

theorem discBoundaryFrame_reconstruct (L : ℂ →L[ℝ] ℂ) {z : ℂ} (hz : z ≠ 0) :
    discBoundaryFrame z (L z) (L (Complex.I * z)) = L := by
  have hq : Complex.normSq z ≠ 0 := mt Complex.normSq_eq_zero.mp hz
  have hq' : z.re ^ 2 + z.im ^ 2 ≠ 0 := by simpa [Complex.normSq_apply, pow_two] using hq
  apply ContinuousLinearMap.ext
  intro h
  rw [discBoundary_linear_coordinates L z, discBoundary_linear_coordinates L (Complex.I * z),
    discBoundary_linear_coordinates L h]
  apply Complex.ext <;>
    simp [discBoundaryFrame, Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
      ContinuousLinearMap.smulRight_apply] <;>
    field_simp [hq'] <;> ring

theorem discBoundary_bilinear_trace (H : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) (z : ℂ) :
    H z z + H (Complex.I * z) (Complex.I * z) =
      Complex.normSq z • (H 1 1 + H Complex.I Complex.I) := by
  have he (a b : ℂ) : H a b =
      a.re • (b.re • H 1 1 + b.im • H 1 Complex.I) +
      a.im • (b.re • H Complex.I 1 + b.im • H Complex.I Complex.I) := by
    conv_lhs => rw [discBoundary_real_coordinates a]
    rw [map_add, map_smul, map_smul, add_apply,
      smul_apply, smul_apply,
      discBoundary_linear_coordinates (H 1) b, discBoundary_linear_coordinates (H Complex.I) b]
  rw [he z z, he (Complex.I * z) (Complex.I * z)]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring

theorem discBoundaryFrame_contDiffOn {s : Set ℂ} {a b : ℂ → ℂ} {n : ℕ∞ω}
    (hs : ∀ z ∈ s, z ≠ 0) (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) :
    ContDiffOn ℝ n (fun z => discBoundaryFrame z (a z) (b z)) s := by
  have hr : ContDiffOn ℝ n (fun z : ℂ => z.re) s := Complex.reCLM.contDiff.contDiffOn
  have hi : ContDiffOn ℝ n (fun z : ℂ => z.im) s := Complex.imCLM.contDiff.contDiffOn
  have hq : ContDiffOn ℝ n Complex.normSq s := (hr.mul hr).add (hi.mul hi)
  have hqi : ContDiffOn ℝ n (fun z => (Complex.normSq z)⁻¹) s :=
    hq.inv (fun z hz => mt Complex.normSq_eq_zero.mp (hs z hz))
  exact (contDiffOn_const.smulRight (hqi.smul ((hr.smul ha).sub (hi.smul hb)))).add
    (contDiffOn_const.smulRight (hqi.smul ((hi.smul ha).add (hr.smul hb))))

theorem discBoundary_fderivWithin_eq {g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    fderivWithin ℝ g (Metric.closedBall (0 : ℂ) 1) z = fderiv ℝ g z :=
  fderivWithin_of_mem_nhds (mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
    Metric.ball_subset_closedBall)

private theorem discBoundaryEuler_eq_ambient_nhds (g : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discBoundaryEuler g =ᶠ[𝓝 z] (fun y => fderiv ℝ g y y) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  rw [discBoundaryEuler, discBoundary_fderivWithin_eq hy]

private theorem discAngular_eq_ambient_nhds (g : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discAngular g =ᶠ[𝓝 z] (fun y => fderiv ℝ g y (Complex.I * y)) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  rw [discAngular, discBoundary_fderivWithin_eq hy]

theorem discBoundaryEuler_hasFDerivAt {g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hz0 : z ≠ 0)
    (hg : ContDiffAt ℝ 2 g z) :
    HasFDerivAt (discBoundaryEuler g)
      (discBoundaryFrame z
        (Complex.normSq z • LeafCandidates.planarLaplacian g z -
          discAngular (discAngular g) z)
        (discBoundaryEuler (discAngular g) z)) z := by
  let L := fderiv ℝ g z
  let H := fderiv ℝ (fderiv ℝ g) z
  let M : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) Complex.I
  have hd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hE : HasFDerivAt (discBoundaryEuler g) (L + H.flip z) z := by
    apply HasFDerivAt.congr_of_eventuallyEq _ (discBoundaryEuler_eq_ambient_nhds g hz)
    simpa [L, H] using hd.hasFDerivAt.clm_apply (hasFDerivAt_id z)
  have hT : HasFDerivAt (discAngular g) (L.comp M + H.flip (Complex.I * z)) z := by
    apply HasFDerivAt.congr_of_eventuallyEq _ (discAngular_eq_ambient_nhds g hz)
    exact hd.hasFDerivAt.clm_apply M.hasFDerivAt
  have hLap : LeafCandidates.planarLaplacian g z = H 1 1 + H Complex.I Complex.I := by
    rw [LeafCandidates.planarLaplacian,
      fderiv_clm_apply hd (differentiableAt_const (1 : ℂ)),
      fderiv_clm_apply hd (differentiableAt_const Complex.I)]
    simp [H, ContinuousLinearMap.flip_apply]
  have hTT : discAngular (discAngular g) z =
      -L z + H (Complex.I * z) (Complex.I * z) := by
    rw [discAngular, discBoundary_fderivWithin_eq hz, hT.fderiv]
    simp [M, ← mul_assoc, ContinuousLinearMap.flip_apply]
  have hET : discBoundaryEuler (discAngular g) z =
      L (Complex.I * z) + H z (Complex.I * z) := by
    rw [discBoundaryEuler, discBoundary_fderivWithin_eq hz, hT.fderiv]
    rfl
  have hA : (L + H.flip z) z =
      Complex.normSq z • LeafCandidates.planarLaplacian g z - discAngular (discAngular g) z := by
    rw [hLap, hTT, ← discBoundary_bilinear_trace H z]
    change L z + H z z = (H z z + H (Complex.I * z) (Complex.I * z)) -
      (-L z + H (Complex.I * z) (Complex.I * z))
    abel
  have hB : (L + H.flip z) (Complex.I * z) = discBoundaryEuler (discAngular g) z := by
    rw [hET]
    change L (Complex.I * z) + H (Complex.I * z) z = L (Complex.I * z) + H z (Complex.I * z)
    rw [hg.isSymmSndFDerivAt (by simp)]
  apply hE.congr_fderiv
  calc
    L + H.flip z = discBoundaryFrame z ((L + H.flip z) z) ((L + H.flip z) (Complex.I * z)) :=
      (discBoundaryFrame_reconstruct _ hz0).symm
    _ = _ := by rw [hA, hB]

end Yau.LeafProofs
