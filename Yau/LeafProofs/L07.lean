import Yau.LeafProofs.L14Exact

/-!
Internal proofs for L07.  All determinant and tensor pairings below use the
actual fibre vector spaces; no curvature or solvability proposition is an input.
-/

noncomputable section

open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix InnerProductSpace
open MeasureTheory Bundle Module

namespace Yau.LeafProofs.L07Aux

open Yau.LeafProofs.L14Aux

section HermitianAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (h : HermitianInnerProduct V)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dualBasis_changeMatrix (b c : Basis ι ℂ V) :
    b.dualBasis.toMatrix c.dualBasis = (c.toMatrix b)ᵀ := by
  ext i j
  simp [Basis.toMatrix_apply, Basis.dualBasis_repr, Basis.dualBasis_apply]

theorem topAlternating_dualBasis_change (b c : Basis ι ℂ V)
    (d : (V →ₗ[ℂ] ℂ) [⋀^ι]→ₗ[ℂ] ℂ) :
    d c.dualBasis = (c.toMatrix b).det * d b.dualBasis := by
  conv_lhs => rw [d.eq_smul_basis_det b.dualBasis]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply,
    dualBasis_changeMatrix, Matrix.det_transpose]
  ring

/-- The determinant metric on the top exterior power is independent of basis.
The determinant factor is paired with the evaluations on the dual basis. -/
theorem determinantDualPairing_basis_independent (b c : Basis ι ℂ V)
    (d e : (V →ₗ[ℂ] ℂ) [⋀^ι]→ₗ[ℂ] ℂ) :
    star (d b.dualBasis) * (hermitianGram h b).det * e b.dualBasis =
      star (d c.dualBasis) * (hermitianGram h c).det * e c.dualBasis := by
  rw [hermitianGram_det_changeBasis h c b,
    topAlternating_dualBasis_change b c d, topAlternating_dualBasis_change b c e,
    star_mul]
  ring

end HermitianAlgebra

section BundleFrames

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem bundleFrameBasis_dualBasis (a x : M.Carrier)
    (hx : x ∈ (localTriv (r := r) E a).baseSet) :
    (bundleFrameBasis (r := r) E a x hx).dualBasis = dualFrame (r := r) E a x := by
  funext i
  apply LinearMap.ext
  intro v
  simp [Basis.dualBasis_apply, bundleFrameBasis_repr, dualFrame]

theorem bundle_metricMatrix_gram (h : Metric E) (a x : M.Carrier)
    (ha : x ∈ (chartAt (ComplexVector n) a).source)
    (hx : x ∈ (localTriv (r := r) E a).baseSet) :
    BundleDbar.metricMatrix (r := r) E h a (chartPt a x) =
      hermitianGram (h x) (bundleFrameBasis (r := r) E a x hx) := by
  unfold BundleDbar.metricMatrix
  rw [chartInv_chartPt_of_mem a x ha]
  ext i j
  simp only [hermitianGram, bundleFrameBasis_apply]

theorem tensorDetLocalPairing_tmul (h : Metric E) (a x : M.Carrier)
    (ha : x ∈ (chartAt (ComplexVector n) a).source)
    (hx : x ∈ (localTriv (r := r) E a).baseSet)
    (u v : E x) (d e : (E x →ₗ[ℂ] ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ) :
    tensorDetLocalPairing (r := r) E h a x (u ⊗ₜ[ℂ] d) (v ⊗ₜ[ℂ] e) =
      star (d (bundleFrameBasis (r := r) E a x hx).dualBasis) *
        (hermitianGram (h x) (bundleFrameBasis (r := r) E a x hx)).det *
        e (bundleFrameBasis (r := r) E a x hx).dualBasis * (h x).toFun u v := by
  simp only [tensorDetLocalPairing, tensorDetCoordinates, TensorProduct.lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, PiLp.smul_apply, smul_eq_mul,
    tensorDetMetricMatrix, bundle_metricMatrix_gram E h a x ha hx,
    ← bundleFrameBasis_dualBasis E a x hx, ← bundleFrameBasis_repr E a x hx,
    Matrix.smul_apply, star_mul]
  rw [← hermitian_coordinates (h x) (bundleFrameBasis (r := r) E a x hx) u v]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorDetLocalPairing_add_left (h : Metric E) (a x : M.Carrier)
    (u v w : TensorDetFiber (r := r) E x) :
    tensorDetLocalPairing (r := r) E h a x (u + v) w =
      tensorDetLocalPairing (r := r) E h a x u w +
        tensorDetLocalPairing (r := r) E h a x v w := by
  simp [tensorDetLocalPairing, map_add, PiLp.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

theorem tensorDetLocalPairing_add_right (h : Metric E) (a x : M.Carrier)
    (u v w : TensorDetFiber (r := r) E x) :
    tensorDetLocalPairing (r := r) E h a x u (v + w) =
      tensorDetLocalPairing (r := r) E h a x u v +
        tensorDetLocalPairing (r := r) E h a x u w := by
  simp [tensorDetLocalPairing, map_add, PiLp.add_apply, mul_add,
    Finset.sum_add_distrib]

/-- The actual determinant-tensor metric descends across every pair of
bundle/chart domains, including zero-rank fibres. -/
theorem tensorDetMetricDescent : LeafCandidates.TensorDetMetricDescent (r := r) E := by
  intro h a b x ha hb hax hbx u
  refine TensorProduct.inductionOn u ?_ ?_
  · intro u d v
    refine TensorProduct.inductionOn v ?_ ?_
    · intro v e
      rw [tensorDetLocalPairing_tmul E h a x ha hax,
        tensorDetLocalPairing_tmul E h b x hb hbx]
      exact congrArg (fun z => z * (h x).toFun u v)
        (determinantDualPairing_basis_independent (h x)
          (bundleFrameBasis (r := r) E a x hax)
          (bundleFrameBasis (r := r) E b x hbx) d e)
    · intro v w hv hw
      rw [tensorDetLocalPairing_add_right, tensorDetLocalPairing_add_right, hv, hw]
  · intro u v hu hv w
    rw [tensorDetLocalPairing_add_left, tensorDetLocalPairing_add_left, hu, hv]

end BundleFrames

section MatrixCalculus

variable {r : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def determinantMultilinear (r : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin r => Fin r → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem determinantMultilinear_apply (A : Matrix (Fin r) (Fin r) ℂ) :
    determinantMultilinear r A = A.det := rfl

theorem determinant_linearDeriv (A D : Matrix (Fin r) (Fin r) ℂ) :
    (determinantMultilinear r).linearDeriv A D =
      ∑ i, (A.updateRow i (D i)).det := by
  exact (determinantMultilinear r).linearDeriv_apply A D

theorem determinant_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    fderiv ℝ (fun w => (H w).det) z v =
      ∑ i, ((H z).updateRow i (fderiv ℝ H z v i)).det := by
  have hd := (((determinantMultilinear r).hasFDerivAt (H z)).restrictScalars ℝ).comp
    z hH.hasFDerivAt
  calc
    _ = (determinantMultilinear r).linearDeriv (H z) (fderiv ℝ H z v) :=
      congrArg (fun f : X →L[ℝ] ℂ => f v) hd.fderiv
    _ = _ := determinant_linearDeriv (H z) (fderiv ℝ H z v)

theorem determinant_updateRow_of_invertible (A D : Matrix (Fin r) (Fin r) ℂ)
    (hA : IsUnit A.det) (i : Fin r) :
    (A.updateRow i (D i)).det = (D * A⁻¹) i i * A.det := by
  have heq : ∑ j, (D * A⁻¹) i j • A j = D i := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change ((D * A⁻¹) * A) i k = D i k
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  rw [← heq, Matrix.det_updateRow_sum, smul_eq_mul]

theorem determinant_fderiv_trace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    fderiv ℝ (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ * fderiv ℝ H z v) := by
  rw [determinant_fderiv H z v hH]
  simp_rw [determinant_updateRow_of_invertible (H z) _ hdet]
  rw [← Finset.sum_mul]
  change Matrix.trace (fderiv ℝ H z v * (H z)⁻¹) * (H z).det = _
  rw [Matrix.trace_mul_comm, mul_comm]

theorem matrix_fderiv_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (i j : Fin r) :
    fderiv ℝ (fun w => H w i j) z v = fderiv ℝ H z v i j := by
  have hrow : DifferentiableAt ℝ (fun w => H w i) z :=
    (differentiableAt_pi.mp hH) i
  have h₁ := congrArg (fun L : X →L[ℝ] ℂ => L v) (fderiv_apply hrow j)
  have h₂ := congrArg (fun L : X →L[ℝ] (Fin r → ℂ) => L v j) (fderiv_apply hH i)
  exact h₁.trans h₂

theorem matrix_wirt_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    (Matrix.of fun i j => wirt (fun w => H w i j) z v) =
      (1 / 2 : ℂ) • (fderiv ℝ H z v - Complex.I • fderiv ℝ H z (Complex.I • v)) := by
  ext i j
  simp only [wirt, matrix_fderiv_entry H z _ hH, Matrix.of_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

theorem determinant_wirt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    wirt (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirt (fun w => H w i j) z v)) := by
  rw [matrix_wirt_eq H z v hH]
  simp only [wirt, determinant_fderiv_trace H z _ hH hdet, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  ring

section WirtingerRules

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (f g : X → ℂ) (z v : X)

theorem wirt_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun w => f w + g w) z v = wirt f z v + wirt g z v := by
  simp only [wirt, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]
  ring

theorem wirt_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun w => f w * g w) z v = wirt f z v * g z + f z * wirt g z v := by
  simp only [wirt, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtBar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtBar (fun w => f w + g w) z v = wirtBar f z v + wirtBar g z v := by
  simp only [wirtBar, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]
  ring

theorem wirtBar_const_mul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtBar (fun w => c * f w) z v = c * wirtBar f z v := by
  simp only [wirtBar, fderiv_const_mul hf c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtBar_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirtBar (fun w => ∑ i ∈ s, f i w) z v = ∑ i ∈ s, wirtBar (f i) z v := by
  simp only [wirtBar, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

end WirtingerRules

theorem matrix_determinant_differentiableAt {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (H : X → Matrix (Fin r) (Fin r) ℂ) (z : X)
    (hH : DifferentiableAt ℝ H z) : DifferentiableAt ℝ (fun w => (H w).det) z :=
  ((((determinantMultilinear r).hasFDerivAt (H z)).restrictScalars ℝ).comp
    z hH.hasFDerivAt).differentiableAt

theorem chernConnectionMatrix_tensorDet {n : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z : ComplexVector n)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) (i : Fin n) :
    BundleDbar.chernConnectionMatrix (fun w => (H w).det • H w) z i =
      BundleDbar.chernConnectionMatrix H z i +
        Matrix.trace (BundleDbar.chernConnectionMatrix H z i) • 1 := by
  have hW : (Matrix.of fun a b =>
      wirt (fun w => ((H w).det • H w) a b) z (stdVec i)) =
        wirt (fun w => (H w).det) z (stdVec i) • H z +
          (H z).det • (Matrix.of fun a b => wirt (fun w => H w a b) z (stdVec i)) := by
    ext a b
    exact wirt_mul (fun w => (H w).det) (fun w => H w a b) z (stdVec i)
      (matrix_determinant_differentiableAt H z hH)
      ((differentiableAt_pi.mp ((differentiableAt_pi.mp hH) a)) b)
  letI : Invertible (H z).det := invertibleOfNonzero hdet.ne_zero
  unfold BundleDbar.chernConnectionMatrix
  dsimp only
  have hi : ((H z).det • H z)⁻¹ = (H z).det⁻¹ • (H z)⁻¹ := by
    exact (Matrix.inv_smul (A := H z) (H z).det hdet).trans (by rw [invOf_eq_inv])
  rw [hW, hi, determinant_wirt H z _ hH hdet]
  simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.nonsing_inv_mul _ hdet, mul_assoc, inv_mul_cancel₀ hdet.ne_zero, one_mul,
    one_smul]
  simp [mul_comm, mul_left_comm, mul_assoc, hdet.ne_zero, add_comm]

theorem matrix_determinant_contDiffOn {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {s : Set X} {k : ℕ∞ω}
    (H : X → Matrix (Fin r) (Fin r) ℂ) (hH : ContDiffOn ℝ k H s) :
    ContDiffOn ℝ k (fun w => (H w).det) s :=
  ((determinantMultilinear r).restrictScalars ℝ).contDiff.comp_contDiffOn hH

theorem matrix_updateRow_contDiffOn {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {s : Set X} {k : ℕ∞ω}
    (H : X → Matrix (Fin r) (Fin r) ℂ) (hH : ContDiffOn ℝ k H s)
    (i : Fin r) (v : Fin r → ℂ) :
    ContDiffOn ℝ k (fun w => (H w).updateRow i v) s := by
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro b
  by_cases hai : a = i
  · subst a
    simpa using (contDiffOn_const : ContDiffOn ℝ k (fun _ : X => v b) s)
  · refine (contDiffOn_pi.mp (contDiffOn_pi.mp hH a) b).congr ?_
    intro w _
    change Function.update (H w) i v a b = H w a b
    exact congrArg (fun row : Fin r → ℂ => row b) (Function.update_of_ne hai v (H w))

theorem matrix_inv_contDiffOn {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {s : Set X} {k : ℕ∞ω}
    (H : X → Matrix (Fin r) (Fin r) ℂ) (hH : ContDiffOn ℝ k H s)
    (hdet : ∀ w ∈ s, (H w).det ≠ 0) :
    ContDiffOn ℝ k (fun w => (H w)⁻¹) s := by
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro b
  have hd := (matrix_determinant_contDiffOn H hH).inv hdet
  have ha := matrix_determinant_contDiffOn _ (matrix_updateRow_contDiffOn H hH b (Pi.single a 1))
  convert! hd.mul ha using 1
  ext w
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply, Pi.inv_apply]

theorem wirt_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {s : Set X} (hs : IsOpen s) (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f s) (v : X) :
    ContDiffOn ℝ ∞ (fun w => wirt f w v) s := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  unfold wirt
  convert! contDiffOn_const.mul
    ((hd.clm_apply contDiffOn_const).sub
      (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))) using 1

theorem chernConnectionMatrix_contDiffOn {n : ℕ}
    {s : Set (ComplexVector n)} (hs : IsOpen s)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ContDiffOn ℝ ∞ H s) (hdet : ∀ w ∈ s, (H w).det ≠ 0) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun w => BundleDbar.chernConnectionMatrix H w i) s := by
  have hinv := matrix_inv_contDiffOn H hH hdet
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro b
  change ContDiffOn ℝ ∞ (fun w => ∑ c, (H w)⁻¹ a c *
    wirt (fun t => H t c b) w (stdVec i)) s
  apply ContDiffOn.sum
  intro c _
  convert! (contDiffOn_pi.mp (contDiffOn_pi.mp hinv a) c).mul
    (wirt_contDiffOn hs (fun w => H w c b)
      (contDiffOn_pi.mp (contDiffOn_pi.mp hH c) b) (stdVec i)) using 1

theorem wirtBar_mul_const {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z v : X) (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtBar (fun w => f w * c) z v = wirtBar f z v * c := by
  simp only [wirtBar, fderiv_mul_const hf c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtBar_trace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : X → Matrix (Fin r) (Fin r) ℂ) (z v : X) (hA : DifferentiableAt ℝ A z) :
    wirtBar (fun w => Matrix.trace (A w)) z v =
      Matrix.trace (Matrix.of fun a b => wirtBar (fun w => A w a b) z v) := by
  exact wirtBar_sum z v Finset.univ (fun a w => A w a a)
    (fun a _ => (differentiableAt_pi.mp (differentiableAt_pi.mp hA a)) a)

theorem wirtBar_eventuallyEq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f g : X → ℂ} {z : X} (hfg : f =ᶠ[𝓝 z] g) (v : X) :
    wirtBar f z v = wirtBar g z v := by
  simp only [wirtBar, hfg.fderiv_eq (𝕜 := ℝ)]

theorem curvatureMatrix_tensorDet {n : ℕ}
    {s : Set (ComplexVector n)} (hs : IsOpen s)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ContDiffOn ℝ ∞ H s) (hdet : ∀ w ∈ s, (H w).det ≠ 0)
    (z : ComplexVector n) (hz : z ∈ s) (i j : Fin n) :
    BundleDbar.curvatureMatrix (fun w => (H w).det • H w) z i j =
      (H z).det • (BundleDbar.curvatureMatrix H z i j +
        Matrix.trace ((H z)⁻¹ * BundleDbar.curvatureMatrix H z i j) • H z) := by
  let A := fun w => BundleDbar.chernConnectionMatrix H w i
  let B : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun a b => wirtBar (fun w => A w a b) z (stdVec j)
  have hA : DifferentiableAt ℝ A z :=
    ((chernConnectionMatrix_contDiffOn hs H hH hdet i).differentiableOn (by simp)).differentiableAt
      (hs.mem_nhds hz)
  have htr : DifferentiableAt ℝ (fun w => Matrix.trace (A w)) z := by
    convert! DifferentiableAt.sum (u := Finset.univ)
      (fun a _ => (differentiableAt_pi.mp (differentiableAt_pi.mp hA a)) a) using 1
    funext w
    simp only [Finset.sum_apply, Matrix.trace, Matrix.diag_apply]
  have hB : (Matrix.of fun a b => wirtBar
      (fun w => BundleDbar.chernConnectionMatrix (fun t => (H t).det • H t) w i a b)
      z (stdVec j)) = B + Matrix.trace B • 1 := by
    ext a b
    have he : (fun w => BundleDbar.chernConnectionMatrix (fun t => (H t).det • H t) w i a b)
        =ᶠ[𝓝 z] (fun w => A w a b + Matrix.trace (A w) * (1 : Matrix (Fin r) (Fin r) ℂ) a b) := by
      filter_upwards [hs.mem_nhds hz] with w hw
      exact congrArg (fun C : Matrix (Fin r) (Fin r) ℂ => C a b)
        (chernConnectionMatrix_tensorDet H w
          ((hH.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hw))
          (isUnit_iff_ne_zero.mpr (hdet w hw)) i)
    change wirtBar
      (fun w => BundleDbar.chernConnectionMatrix (fun t => (H t).det • H t) w i a b)
      z (stdVec j) = B a b + Matrix.trace B * (1 : Matrix (Fin r) (Fin r) ℂ) a b
    rw [wirtBar_eventuallyEq he]
    rw [wirtBar_add _ _ z _
      ((differentiableAt_pi.mp (differentiableAt_pi.mp hA a)) b)
      (htr.mul_const _), wirtBar_mul_const _ z _ _ htr, wirtBar_trace A z _ hA]
    rfl
  have hR : BundleDbar.curvatureMatrix H z i j = -(H z * B) := rfl
  have htrace : Matrix.trace ((H z)⁻¹ * BundleDbar.curvatureMatrix H z i j) =
      -Matrix.trace B := by
    rw [hR, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)), Matrix.one_mul,
      Matrix.trace_neg]
  rw [htrace, hR]
  unfold BundleDbar.curvatureMatrix
  dsimp only
  rw [hB]
  change -((H z).det • H z * (B + Matrix.trace B • 1)) = _
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    smul_add, smul_neg, neg_smul, neg_add_rev, smul_smul, mul_comm]
  abel

end MatrixCalculus

section BundleCurvature

open BundleDbar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem bundle_localDomain_isOpen (a : M.Carrier) :
    IsOpen (localDomain (r := r) E a) := by
  exact (continuousOn_extChartAt_symm (I := ComplexModel n) a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (localTriv (r := r) E a).open_baseSet

theorem bundle_metricMatrix_posDef (h : Metric E) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    (BundleDbar.metricMatrix (r := r) E h a z).PosDef := by
  have heq : BundleDbar.metricMatrix (r := r) E h a z =
      hermitianGram (h (chartInv a z))
        (bundleFrameBasis (r := r) E a (chartInv a z) hz.2) := by
    ext i j
    simp only [BundleDbar.metricMatrix, hermitianGram, bundleFrameBasis_apply]
  rw [heq]
  exact hermitianGram_posDef _ _

theorem bundle_metricMatrix_det_ne_zero (h : Metric E) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    (BundleDbar.metricMatrix (r := r) E h a z).det ≠ 0 :=
  ((bundle_metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero

/-- The exact tensor-determinant curvature identity in the locked L07 target.
Holomorphicity is retained in its original interface; the local metric
calculation itself only uses smoothness and the positive Gram matrices. -/
theorem tensorDetCurvatureIdentity :
    LeafCandidates.TensorDetCurvatureIdentity (r := r) E := by
  intro h _ hsm a z hz i j
  have hm : ContDiffOn ℝ ∞ (BundleDbar.metricMatrix (r := r) E h a)
      (localDomain (r := r) E a) :=
    contDiffOn_pi.mpr fun α => contDiffOn_pi.mpr fun β => hsm a α β
  exact curvatureMatrix_tensorDet (bundle_localDomain_isOpen E a)
    (BundleDbar.metricMatrix (r := r) E h a) hm
    (fun w hw => bundle_metricMatrix_det_ne_zero E h a w hw) z hz i j

end BundleCurvature

section PositivityAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[instance_reducible]
def hermitianInnerProductCore (h : HermitianInnerProduct V) : InnerProductSpace.Core ℂ V where
  inner := h.toFun
  conj_inner_symm u v := (h.conjugate_symmetric u v).symm
  re_inner_nonneg u := (h.positive_definite u).1
  add_left := h.map_add_left
  smul_left u v c := h.map_smul_left c u v
  definite u hu := (h.positive_definite u).2.mp (by rw [hu]; rfl)

theorem hermitian_exists_orthonormal_basis {r : ℕ} (h : HermitianInnerProduct V)
    (b : Basis (Fin r) ℂ V) :
    ∃ c : Basis (Fin r) ℂ V, hermitianGram h c = 1 := by
  letI : InnerProductSpace.Core ℂ V := hermitianInnerProductCore h
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hdim : Module.finrank ℂ V = r := by simpa using Module.finrank_eq_card_basis b
  let c : OrthonormalBasis (Fin r) ℂ V :=
    (stdOrthonormalBasis ℂ V).reindex (finCongr hdim)
  refine ⟨c.toBasis, ?_⟩
  ext i j
  change ⟪c i, c j⟫_ℂ = (1 : Matrix (Fin r) (Fin r) ℂ) i j
  simp [c.inner_eq_ite, Matrix.one_apply]

/-- Eight equally weighted scalar samples matching the complex Gaussian
moments needed in the Demailly--Skoda argument through degree four. -/
def phaseSample (k : Fin 8) : ℂ := ![0, 0, 0, 0, 1, -1, Complex.I, -Complex.I] k

def phaseMoment (p q : ℕ) : ℂ :=
  (8 : ℂ)⁻¹ * ∑ k : Fin 8, star (phaseSample k) ^ p * phaseSample k ^ q

theorem phaseMoment_eq (p q : ℕ) (hp : p ≤ 2) (hq : q ≤ 2) :
    phaseMoment p q = if p = q then (if p = 0 then 1 else 1 / 2) else 0 := by
  interval_cases p <;> interval_cases q <;>
    norm_num [phaseMoment, phaseSample, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.I_sq]

def phaseAverage (ι : Type*) [Fintype ι] [DecidableEq ι] : ((ι → Fin 8) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∏ _ : ι, (8 : ℂ)⁻¹) * ∑ η : ι → Fin 8, f η
  map_add' f g := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem phaseAverage_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Fin 8 → ℂ) :
    phaseAverage ι (fun η => ∏ a, g a (η a)) =
      ∏ a, ((8 : ℂ)⁻¹ * ∑ k : Fin 8, g a k) := by
  classical
  change (∏ _ : ι, (8 : ℂ)⁻¹) * (∑ η : ι → Fin 8, ∏ a, g a (η a)) = _
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa using Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 8)) g

theorem phaseAverage_re_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Fin 8) → ℂ) (hf : ∀ η, 0 ≤ (f η).re) :
    0 ≤ (phaseAverage ι f).re := by
  have hc : (∏ _ : ι, (8 : ℂ)⁻¹) = Complex.ofReal (∏ _ : ι, (8 : ℝ)⁻¹) := by simp
  change 0 ≤ ((∏ _ : ι, (8 : ℂ)⁻¹) * ∑ η : ι → Fin 8, f η).re
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => by norm_num)
    (Finset.sum_nonneg fun η _ => hf η)

def phaseFactor {ι : Type*} [DecidableEq ι] (a γ δ α β : ι) (k : Fin 8) : ℂ :=
  (if a = γ then star (phaseSample k) else 1) *
    (if a = δ then phaseSample k else 1) *
    (if a = α then star (phaseSample k) else 1) *
    (if a = β then phaseSample k else 1)

def phaseFactorMoment {ι : Type*} [DecidableEq ι] (a γ δ α β : ι) : ℂ :=
  (8 : ℂ)⁻¹ * ∑ k : Fin 8, phaseFactor a γ δ α β k

theorem phaseFactorMoment_eq {ι : Type*} [DecidableEq ι] (a γ δ α β : ι) :
    phaseFactorMoment a γ δ α β =
      phaseMoment ((if a = γ then 1 else 0) + (if a = α then 1 else 0))
        ((if a = δ then 1 else 0) + (if a = β then 1 else 0)) := by
  unfold phaseFactorMoment phaseMoment
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold phaseFactor
  split_ifs <;> simp_all [pow_succ] <;> ring

theorem phaseAverage_fourth_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ δ α β : ι) :
    phaseAverage ι (fun η => star (phaseSample (η γ)) * phaseSample (η δ) *
      star (phaseSample (η α)) * phaseSample (η β)) =
      ∏ a, phaseFactorMoment a γ δ α β := by
  have heq : (fun η : ι → Fin 8 => star (phaseSample (η γ)) * phaseSample (η δ) *
      star (phaseSample (η α)) * phaseSample (η β)) =
      (fun η => ∏ a, phaseFactor a γ δ α β (η a)) := by
    funext η
    simp only [phaseFactor, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  rw [heq]
  exact phaseAverage_prod _

theorem phaseAverage_paired {ι : Type*} [Fintype ι] [DecidableEq ι] (γ α : ι) :
    phaseAverage ι (fun η => star (phaseSample (η γ)) * phaseSample (η γ) *
      star (phaseSample (η α)) * phaseSample (η α)) =
        if γ = α then (1 / 2 : ℂ) else 1 / 4 := by
  rw [phaseAverage_fourth_prod]
  by_cases h : γ = α
  · subst α
    have hm : ∀ a, phaseFactorMoment a γ γ γ γ = if a = γ then 1 / 2 else 1 := by
      intro a
      by_cases ha : a = γ <;> simp [phaseFactorMoment_eq, ha, phaseMoment_eq]
    simp only [hm, Fintype.prod_ite_eq', ↓reduceIte]
  · have hm : ∀ a, phaseFactorMoment a γ γ α α =
        (if a = γ then (1 / 2 : ℂ) else 1) * (if a = α then 1 / 2 else 1) := by
      intro a
      by_cases ha : a = γ <;> by_cases hb : a = α <;>
        simp_all [phaseFactorMoment_eq, phaseMoment_eq]
    simp only [hm, Finset.prod_mul_distrib, Fintype.prod_ite_eq', h, ↓reduceIte]
    norm_num

theorem phaseFactorMoment_zero_unmatched {ι : Type*} [DecidableEq ι]
    (γ δ α β : ι) (hγδ : γ ≠ δ) (hγβ : γ ≠ β) :
    phaseFactorMoment γ γ δ α β = 0 := by
  by_cases hγα : γ = α <;> simp_all [phaseFactorMoment_eq, phaseMoment_eq]

theorem phaseFactorMoment_zero_after_pair {ι : Type*} [DecidableEq ι]
    (γ α β : ι) (hαβ : α ≠ β) :
    phaseFactorMoment α γ γ α β = 0 := by
  by_cases hαγ : α = γ <;> simp_all [phaseFactorMoment_eq, phaseMoment_eq]

theorem phaseFactorMoment_zero_after_cross_pair {ι : Type*} [DecidableEq ι]
    (γ δ α : ι) (hαδ : α ≠ δ) :
    phaseFactorMoment α γ δ α γ = 0 := by
  by_cases hαγ : α = γ <;> simp_all [phaseFactorMoment_eq, phaseMoment_eq]

/-- Exact fourth-moment identity for the finite positive average. -/
theorem phaseAverage_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ δ α β : ι) :
    phaseAverage ι (fun η => star (phaseSample (η γ)) * phaseSample (η δ) *
      star (phaseSample (η α)) * phaseSample (η β)) =
      ((if γ = δ ∧ α = β then (1 : ℂ) else 0) +
        (if γ = β ∧ α = δ then 1 else 0)) / 4 := by
  by_cases hγδ : γ = δ
  · subst δ
    by_cases hαβ : α = β
    · subst β
      rw [phaseAverage_paired]
      by_cases hγα : γ = α <;> simp [hγα, eq_comm] <;> norm_num
    · have hz : (∏ a, phaseFactorMoment a γ γ α β) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ α) (phaseFactorMoment_zero_after_pair γ α β hαβ)
      rw [phaseAverage_fourth_prod, hz]
      have hn : ¬(γ = β ∧ α = γ) := by aesop
      simp [hαβ, hn]
  · by_cases hγβ : γ = β
    · subst β
      by_cases hαδ : α = δ
      · subst δ
        have heq : (fun η : ι → Fin 8 => star (phaseSample (η γ)) * phaseSample (η α) *
            star (phaseSample (η α)) * phaseSample (η γ)) =
            (fun η => star (phaseSample (η γ)) * phaseSample (η γ) *
              star (phaseSample (η α)) * phaseSample (η α)) := by
          funext η
          ring
        rw [heq, phaseAverage_paired]
        simp [hγδ]
      · have hz : (∏ a, phaseFactorMoment a γ δ α γ) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ α)
            (phaseFactorMoment_zero_after_cross_pair γ δ α hαδ)
        rw [phaseAverage_fourth_prod, hz]
        simp [hγδ, hαδ]
    · have hz : (∏ a, phaseFactorMoment a γ δ α β) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ γ) (phaseFactorMoment_zero_unmatched γ δ α β hγδ hγβ)
      rw [phaseAverage_fourth_prod, hz]
      simp [hγδ, hγβ]

theorem phaseAverage_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (f : κ → (ι → Fin 8) → ℂ) :
    phaseAverage ι (fun η => ∑ k ∈ s, f k η) = ∑ k ∈ s, phaseAverage ι (f k) := by
  convert! map_sum (phaseAverage ι) f s using 1
  apply congrArg (phaseAverage ι)
  funext η
  simp only [Finset.sum_apply]

theorem phaseAverage_const_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (f : (ι → Fin 8) → ℂ) :
    phaseAverage ι (fun η => c * f η) = c * phaseAverage ι f := by
  convert! (phaseAverage ι).map_smul c f using 1

theorem phaseAverage_fourth_contraction {n r : ℕ}
    (R : Fin n → Fin n → Fin r → Fin r → ℂ) (U : Fin n → Fin r → ℂ) :
    phaseAverage (Fin r) (fun η => ∑ i, ∑ j, ∑ α, ∑ β, ∑ γ, ∑ δ,
      (R i j α β * U i γ * star (U j δ)) *
        (star (phaseSample (η γ)) * phaseSample (η δ) *
          star (phaseSample (η α)) * phaseSample (η β))) =
      (∑ i, ∑ j, ∑ α, ∑ β,
        (R i j α α * U i β * star (U j β) +
          R i j α β * U i β * star (U j α))) / 4 := by
  simp only [phaseAverage_sum, phaseAverage_const_mul, phaseAverage_fourth,
    ← mul_div_assoc, ← Finset.sum_div]
  apply congrArg (fun z : ℂ => z / 4)
  simp only [mul_add, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem skoda_finite_expansion {r : ℕ} (c : ℂ) (u v x : Fin r → ℂ) (α β : Fin r) :
    c * (∑ γ, u γ * star (x γ)) * star (∑ δ, v δ * star (x δ)) * star (x α) * x β =
      ∑ γ, ∑ δ, (c * u γ * star (v δ)) * (star (x γ) * x δ * star (x α) * x β) := by
  simp only [star_sum, star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro δ _
  ring

/-- The finite-dimensional Demailly--Skoda positivity calculation in a
Hermitian orthonormal frame, before change of fibre basis. -/
theorem skoda_orthonormal_sum_nonneg {n r : ℕ}
    (R : Fin n → Fin n → Fin r → Fin r → ℂ)
    (hR : ∀ (ξ : ComplexVector n) (v : ComplexVector r),
      0 ≤ BundleDbar.griffithsQuadratic (fun i j => Matrix.of (R i j)) ξ v)
    (U : Fin n → Fin r → ℂ) :
    0 ≤ (∑ i, ∑ j, ∑ α, ∑ β,
      (R i j α α * U i β * star (U j β) +
        R i j α β * U i β * star (U j α))).re := by
  let F : (Fin r → Fin 8) → ℂ := fun η => ∑ i, ∑ j, ∑ α, ∑ β, ∑ γ, ∑ δ,
    (R i j α β * U i γ * star (U j δ)) *
      (star (phaseSample (η γ)) * phaseSample (η δ) *
        star (phaseSample (η α)) * phaseSample (η β))
  have hF : ∀ η, 0 ≤ (F η).re := by
    intro η
    let ξ : ComplexVector n := WithLp.toLp 2 (fun i => ∑ γ, U i γ * star (phaseSample (η γ)))
    let v : ComplexVector r := WithLp.toLp 2 (fun α => phaseSample (η α))
    have hq := hR ξ v
    change 0 ≤ (∑ i, ∑ j, ∑ α, ∑ β,
      R i j α β * (∑ γ, U i γ * star (phaseSample (η γ))) *
        star (∑ δ, U j δ * star (phaseSample (η δ))) *
          star (phaseSample (η α)) * phaseSample (η β)).re at hq
    simpa only [skoda_finite_expansion] using hq
  have hp := phaseAverage_re_nonneg F hF
  change 0 ≤ (phaseAverage (Fin r) F).re at hp
  have heq := phaseAverage_fourth_contraction R U
  change phaseAverage (Fin r) F = _ at heq
  rw [heq] at hp
  have hdiv (q : ℂ) : (q / 4).re = q.re / 4 := by norm_num [Complex.div_re]
  rw [hdiv] at hp
  linarith only [hp]

theorem skoda_trace_sum {r : ℕ} (R : Fin r → Fin r → ℂ) (u v : Fin r → ℂ) :
    (∑ α, ∑ β, R α α * u β * star (v β)) =
      ∑ β, Matrix.trace (Matrix.of R) * star (v β) * u β := by
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro α _
  ring

theorem skoda_trace_correction_entry {r : ℕ} (R : Fin r → Fin r → ℂ)
    (u v : Fin r → ℂ) :
    (∑ α : Fin r, ∑ β : Fin r, (R α α * u β * star (v β) + R α β * u β * star (v α))) =
      ∑ α : Fin r, ∑ β : Fin r, (Matrix.of R + Matrix.trace (Matrix.of R) •
        (1 : Matrix (Fin r) (Fin r) ℂ)) α β * star (v α) * u β := by
  have ht := skoda_trace_sum R u v
  have hn : (∑ α : Fin r, ∑ β : Fin r, R α β * u β * star (v α)) =
      ∑ α : Fin r, ∑ β : Fin r, R α β * star (v α) * u β := by
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    one_mul, zero_mul, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [ht, hn, add_comm]

theorem skoda_orthonormal_nonneg {n r : ℕ}
    (R : Fin n → Fin n → Fin r → Fin r → ℂ)
    (hR : ∀ (ξ : ComplexVector n) (v : ComplexVector r),
      0 ≤ BundleDbar.griffithsQuadratic (fun i j => Matrix.of (R i j)) ξ v)
    (U : Fin n → Fin r → ℂ) :
    0 ≤ BundleDbar.nakanoQuadratic (fun i j => Matrix.of (R i j) +
      Matrix.trace (Matrix.of (R i j)) • (1 : Matrix (Fin r) (Fin r) ℂ)) U := by
  have h := skoda_orthonormal_sum_nonneg R hR U
  simpa only [skoda_trace_correction_entry, BundleDbar.nakanoQuadratic] using h

theorem sesquilinear_matrix_sum {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    (∑ α : Fin r, ∑ β : Fin r, A α β * star (v α) * u β) =
      star v ⬝ᵥ (A *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem sesquilinear_matrix_conjugate {r : ℕ} (A T : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    (∑ α : Fin r, ∑ β : Fin r, (Tᴴ * A * T) α β * star (v α) * u β) =
      ∑ α : Fin r, ∑ β : Fin r, A α β * star ((T *ᵥ v) α) * (T *ᵥ u) β := by
  rw [sesquilinear_matrix_sum, sesquilinear_matrix_sum]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc]

theorem nakanoQuadratic_conjugate {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (U : Fin n → Fin r → ℂ) :
    BundleDbar.nakanoQuadratic (fun i j => Tᴴ * R i j * T) U =
      BundleDbar.nakanoQuadratic R (fun i => T *ᵥ U i) := by
  unfold BundleDbar.nakanoQuadratic
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact sesquilinear_matrix_conjugate (R i j) T (U i) (U j)

theorem griffithsQuadratic_conjugate {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (ξ : ComplexVector n) (v : ComplexVector r) :
    BundleDbar.griffithsQuadratic (fun i j => Tᴴ * R i j * T) ξ v =
      BundleDbar.griffithsQuadratic R ξ (WithLp.toLp 2 (T *ᵥ fun α => v α)) := by
  have hfactor (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (i j : Fin n) :
      (∑ α : Fin r, ∑ β : Fin r, A α β * ξ i * star (ξ j) * star (w α) * w β) =
        ξ i * star (ξ j) * (∑ α : Fin r, ∑ β : Fin r, A α β * star (w α) * w β) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  unfold BundleDbar.griffithsQuadratic
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hfactor, hfactor]
  exact congrArg (fun z => ξ i * star (ξ j) * z)
    (sesquilinear_matrix_conjugate (R i j) T (fun α => v α) (fun α => v α))

theorem hermitianGram_inv_factor {r : ℕ} (h : HermitianInnerProduct V)
    (b c : Basis (Fin r) ℂ V) (hc : hermitianGram h c = 1) :
    (hermitianGram h b)⁻¹ = b.toMatrix c * (b.toMatrix c)ᴴ := by
  let T := b.toMatrix c
  let S := c.toMatrix b
  have hts : T * S = 1 := b.toMatrix_mul_toMatrix_flip c
  have ht : Tᴴ * hermitianGram h b * T = 1 :=
    (hermitianGram_changeBasis h b c).symm.trans hc
  apply Matrix.inv_eq_left_inv
  change (T * Tᴴ) * hermitianGram h b = 1
  calc
    _ = ((T * Tᴴ) * hermitianGram h b) * (T * S) := by rw [hts, Matrix.mul_one]
    _ = T * (Tᴴ * hermitianGram h b * T) * S := by noncomm_ring
    _ = 1 := by rw [ht, Matrix.mul_one, hts]

/-- The pointwise Demailly--Skoda inequality for every positive Hermitian
Gram matrix, with the inverse metric appearing in its trace contraction. -/
theorem skoda_hermitianGram_nonneg {n r : ℕ} (h : HermitianInnerProduct V)
    (b : Basis (Fin r) ℂ V)
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hR : ∀ (ξ : ComplexVector n) (v : ComplexVector r),
      0 ≤ BundleDbar.griffithsQuadratic R ξ v)
    (U : Fin n → Fin r → ℂ) :
    0 ≤ BundleDbar.nakanoQuadratic
      (fun i j => R i j + Matrix.trace ((hermitianGram h b)⁻¹ * R i j) • hermitianGram h b) U := by
  obtain ⟨c, hc⟩ := hermitian_exists_orthonormal_basis h b
  let T := b.toMatrix c
  let S := c.toMatrix b
  let R' := fun i j => Tᴴ * R i j * T
  have hts : T * S = 1 := b.toMatrix_mul_toMatrix_flip c
  have ht : Tᴴ * hermitianGram h b * T = 1 :=
    (hermitianGram_changeBasis h b c).symm.trans hc
  have hi : (hermitianGram h b)⁻¹ = T * Tᴴ := hermitianGram_inv_factor h b c hc
  have hp : ∀ (ξ : ComplexVector n) (v : ComplexVector r),
      0 ≤ BundleDbar.griffithsQuadratic R' ξ v := by
    intro ξ v
    rw [griffithsQuadratic_conjugate]
    exact hR _ _
  have hn := skoda_orthonormal_nonneg (fun i j α β => R' i j α β) hp
    (fun i => S *ᵥ U i)
  have heq : (fun i j => Tᴴ *
      (R i j + Matrix.trace ((hermitianGram h b)⁻¹ * R i j) • hermitianGram h b) * T) =
      (fun i j => R' i j + Matrix.trace (R' i j) • (1 : Matrix (Fin r) (Fin r) ℂ)) := by
    funext i j
    have htrace : Matrix.trace (R' i j) = Matrix.trace ((hermitianGram h b)⁻¹ * R i j) := by
      change Matrix.trace (Tᴴ * R i j * T) = _
      rw [Matrix.trace_mul_cycle, ← hi]
    rw [htrace]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ht]
    rfl
  change 0 ≤ BundleDbar.nakanoQuadratic
    (fun i j => R' i j + Matrix.trace (R' i j) • (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun i => S *ᵥ U i) at hn
  rw [← heq, nakanoQuadratic_conjugate] at hn
  simpa only [Matrix.mulVec_mulVec, hts, Matrix.one_mulVec] using hn

theorem nakanoQuadratic_smul_real {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (c : ℂ) (hc : c.im = 0) (U : Fin n → Fin r → ℂ) :
    BundleDbar.nakanoQuadratic (fun i j => c • R i j) U =
      c.re * BundleDbar.nakanoQuadratic R U := by
  simp only [BundleDbar.nakanoQuadratic, Matrix.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, Complex.mul_re, hc, zero_mul, sub_zero]

theorem hermitianGram_det_nonneg {r : ℕ} (h : HermitianInnerProduct V)
    (b : Basis (Fin r) ℂ V) : 0 ≤ (hermitianGram h b).det :=
  (hermitianGram_posDef h b).posSemidef.det_nonneg

theorem hermitianGram_det_im {r : ℕ} (h : HermitianInnerProduct V)
    (b : Basis (Fin r) ℂ V) : (hermitianGram h b).det.im = 0 := by
  have hs : star (hermitianGram h b).det = (hermitianGram h b).det := by
    rw [← Matrix.det_conjTranspose, (hermitianGram_isHermitian h b).eq]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end PositivityAlgebra

section BundleSkoda

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Full Griffiths-semi-positive to determinant-tensor Nakano-semi-positive
implication, using the computed curvature and no extra curvature assumption. -/
theorem demaillySkoda : LeafCandidates.DemaillySkoda (r := r) E := by
  intro h hhol hsm hG a z hz U
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let b := bundleFrameBasis (r := r) E a (chartInv a z) hz.2
  have hH : H = hermitianGram (h (chartInv a z)) b := by
    ext i j
    simp only [H, b, BundleDbar.metricMatrix, hermitianGram, bundleFrameBasis_apply]
  have hcurv : curvatureMatrix (tensorDetMetricMatrix (r := r) E h a) z =
      (fun i j => H.det • (curvature (r := r) E h a z i j +
        Matrix.trace (H⁻¹ * curvature (r := r) E h a z i j) • H)) := by
    funext i j
    exact tensorDetCurvatureIdentity E h hhol hsm a z hz i j
  rw [hcurv]
  rw [nakanoQuadratic_smul_real _ H.det (by rw [hH]; exact hermitianGram_det_im _ _) U]
  apply mul_nonneg
  · exact (Complex.nonneg_iff.mp (hH ▸ hermitianGram_det_nonneg (h (chartInv a z)) b)).1
  · rw [hH]
    exact skoda_hermitianGram_nonneg (h (chartInv a z)) b
      (curvature (r := r) E h a z) (hG a z hz) U

end BundleSkoda

end Yau.LeafProofs.L07Aux

namespace Yau.LeafProofs

/-- The exact original L07 obligation, including the genuine determinant-tensor
metric and curvature computations and the shared weighted solvability theorem. -/
theorem L07 : Yau.LeafObligations.L07 := by
  refine ⟨?_, L14⟩
  intro n r M E _ _ _ _ _ _ _
  exact ⟨L07Aux.tensorDetMetricDescent E, L07Aux.tensorDetCurvatureIdentity E,
    L07Aux.demaillySkoda E⟩

end Yau.LeafProofs
