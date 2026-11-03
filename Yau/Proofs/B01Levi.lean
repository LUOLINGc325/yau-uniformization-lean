import Yau.Proofs.B01Source
import Yau.Proofs.B01Metric

open scoped Manifold Topology ContDiff
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation
open LeafProofs.L14Aux

theorem wirt_congr_of_eventuallyEq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f g : V → ℂ} {z : V} (he : f =ᶠ[𝓝 z] g) (v : V) : wirt f z v = wirt g z v := by
  unfold wirt
  rw [he.fderiv_eq]

theorem scalar_wirt_smul_direction (f : ℂ → ℂ) (z a : ℂ) :
    wirt f z a = a * wirt f z 1 := by
  simpa only [wirtBar_star, star_star, star_mul, smul_eq_mul, mul_one, mul_comm] using
    congrArg star (wirtBar_smul_direction (fun t => star (f t)) z (1 : ℂ) a)

theorem scalar_wirtBar_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : V → ℂ) (f : ℂ → ℂ) (z v : V)
    (hT : DifferentiableAt ℂ T z) (hf : DifferentiableAt ℝ f (T z)) :
    wirtBar (fun u => f (T u)) z v =
      star (fderiv ℂ T z v) * wirtBar f (T z) 1 := by
  rw [wirtBar_comp_complex_differentiable T f z v hT hf]
  simpa only [smul_eq_mul, mul_one] using
    wirtBar_smul_direction f (T z) (1 : ℂ) (fderiv ℂ T z v)

theorem scalar_mixed_im_zero {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    (wirt (fun u : ℂ => wirtBar (fun t : ℂ => (f t : ℂ)) u 1) z 1).im = 0 := by
  have hi := (LeafProofs.L18Aux.leviMatrix_entry_re_im hf (fun _ : Fin 1 => (1 : ℂ)) 0 0).2
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (wirt (fun u : ℂ => wirtBar (fun t : ℂ => (f t : ℂ)) u 1) z 1).im = _ at hi
  rw [hs (1 : ℂ) (Complex.I • (1 : ℂ)), sub_self, mul_zero] at hi
  exact hi

theorem scalar_levi_comp (T : ComplexVector 1 → ℂ) (f : ℂ → ℝ)
    (O : Set (ComplexVector 1)) (U : Set ℂ) (hO : IsOpen O) (hU : IsOpen U)
    (hT : ContDiffOn ℂ ∞ T O) (hf : ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo T O U) (z : ComplexVector 1) (hz : z ∈ O) :
    wirt (fun u => wirtBar (fun t => (f (T t) : ℂ)) u (stdVec 0)) z (stdVec 0) =
      (Complex.normSq (fderiv ℂ T z (stdVec 0)) : ℂ) *
        wirt (fun u : ℂ => wirtBar (fun t : ℂ => (f t : ℂ)) u 1) (T z) 1 := by
  let A : ComplexVector 1 → ℂ := fun w => fderiv ℂ T w (stdVec 0)
  let B : ℂ → ℂ := fun u => wirtBar (fun t : ℂ => (f t : ℂ)) u 1
  have hA : ContDiffOn ℂ ∞ A O :=
    (hT.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hfC : ContDiffOn ℝ ∞ (fun t : ℂ => (f t : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hB : ContDiffOn ℝ ∞ B U := wirtBar_contDiffOn hU _ hfC (1 : ℂ)
  have hTc := (hT.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAc := (hA.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hBc := (hB.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by simp)
  have hlocal : (fun w => wirtBar (fun t => (f (T t) : ℂ)) w (stdVec 0)) =ᶠ[𝓝 z]
      (fun w => star (A w) * B (T w)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact scalar_wirtBar_comp T _ w (stdVec 0)
      ((hT.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
      ((hfC.contDiffAt (hU.mem_nhds (hmap hw))).differentiableAt (by simp))
  rw [wirt_congr_of_eventuallyEq hlocal]
  have hAs : DifferentiableAt ℝ (fun w => star (A w)) z :=
    Complex.conjCLE.differentiableAt.comp z (hAc.restrictScalars ℝ)
  have hBs : DifferentiableAt ℝ (fun w => B (T w)) z := hBc.comp z (hTc.restrictScalars ℝ)
  rw [wirt_mul_rule (fun w => star (A w)) (fun w => B (T w)) z (stdVec 0) hAs hBs]
  rw [wirt_star, wirtBar_eq_zero_of_complex_differentiable A z (stdVec 0) hAc,
    star_zero, zero_mul, zero_add,
    wirt_comp_complex_differentiable T B z (stdVec 0) hTc hBc,
    scalar_wirt_smul_direction]
  change star (A z) * (A z * wirt B (T z) 1) = _
  rw [← mul_assoc, mul_comm (star (A z)) (A z)]
  rw [Complex.star_def, Complex.mul_conj]

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

include r E in
theorem discLevi_inChart (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier) {z : ComplexVector 1}
    (hz : z ∈ chartTarget a) :
    leviC (inChart a φ) z 0 0 =
      ((discLeviScalar c φ (chartInv a z) *
        Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) : ℝ) : ℂ) := by
  let T : ComplexVector 1 → ℂ := fun w => c (chartInv a w)
  let f : ℂ → ℝ := fun t => φ (c.symm t)
  have hT : ContDiffOn ℂ ∞ T (chartTarget a) :=
    fun w hw => (disc_inChart_contDiffAt c hc a hw).contDiffWithinAt
  have hf : ContDiffOn ℝ ∞ f puncturedUnitDisc := smoothFn_in_disc (r := r) E c hc φ hφ
  have hm : MapsTo T (chartTarget a) puncturedUnitDisc := fun w _ => disc_mem c hc (chartInv a w)
  have hcomp := scalar_levi_comp T f (chartTarget a) puncturedUnitDisc
    (isOpen_extChartAt_target a) puncturedUnitDisc_isOpen hT hf hm z hz
  have he : (fun t => (f (T t) : ℂ)) = (fun t => ((φ (chartInv a t) : ℝ) : ℂ)) := by
    funext t
    dsimp only [f, T, inChart]
    rw [disc_left_inv c hc]
  rw [he] at hcomp
  have him := scalar_mixed_im_zero
    ((hf.contDiffAt (puncturedUnitDisc_isOpen.mem_nhds (hm hz))).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞))
  have hreal : wirt (fun u : ℂ => wirtBar (fun t : ℂ => (f t : ℂ)) u 1) (T z) 1 =
      (discLeviScalar c φ (chartInv a z) : ℂ) := by
    apply Complex.ext
    · rfl
    · exact him
  rw [hreal] at hcomp
  have hJ : fderiv ℂ T z (stdVec 0) = wirt (fun w => c (chartInv a w)) z (stdVec 0) :=
    (wirt_eq_fderiv_of_complex_differentiable T z (stdVec 0)
      ((hT.contDiffAt ((isOpen_extChartAt_target a).mem_nhds hz)).differentiableAt (by simp))).symm
  rw [hJ] at hcomp
  change leviC (inChart a φ) z 0 0 = _ at hcomp
  exact hcomp.trans (by rw [← Complex.ofReal_mul]; congr 1; ring)

end Yau.Proofs.B01Aux
