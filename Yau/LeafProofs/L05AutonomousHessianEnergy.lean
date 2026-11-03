import Yau.LeafProofs.L05AutonomousSlopes
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- For the actual real symmetric matrix, the trace square is its Frobenius square. -/
theorem auto_trace_square_eq_frobenius {n : ℕ} (H : Mat n) (hH : H.IsHermitian) :
    Matrix.trace (H*H)=‖H‖^2 := by
  rw [frobenius_norm_sq]
  change (∑ i, ∑ j, H i j*H j i)=∑ i, ∑ j, (H i j)^2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : H j i=H i j := by simpa only [star_trivial] using hH.apply i j
  rw [hs,pow_two]

/-- This is a trace of a genuine symmetric square after conjugation by sqrt A. -/
theorem auto_trace_HAHA_nonneg {n : ℕ} {A H : Mat n}
    (hA : A.PosSemidef) (hH : H.IsHermitian) : 0≤Matrix.trace (A*H*A*H) := by
  let S := CFC.sqrt A
  have hS : S.conjTranspose=S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hSS : S*S=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  let B := S*H*S
  have hB : B.IsHermitian := by
    have hh := Matrix.isHermitian_conjTranspose_mul_mul S hH
    simpa only [hS,B] using hh
  have hBB : (B*B).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self B
    rwa [hB.eq] at hh
  have heq : B*B=S*(H*A*H)*S := by
    dsimp only [B]
    rw [← hSS]
    noncomm_ring
  calc
    0 ≤ Matrix.trace (B*B) := hBB.trace_nonneg
    _ = Matrix.trace (A*H*A*H) := by
      rw [heq,Matrix.trace_mul_cycle,hSS]
      simp only [Matrix.mul_assoc]

/-- The pointwise algebra behind the constant elliptic L² identity. -/
theorem auto_elliptic_trace_hessian_sq {n : ℕ} {ell : ℝ} (hell : 0≤ell)
    (A H : Mat n) (hA : (A-ell • (1 : Mat n)).PosSemidef) (hH : H.IsHermitian) :
    ell^2*‖H‖^2≤Matrix.trace (A*H*A*H) := by
  let P := A-ell • (1 : Mat n)
  have hP : P.PosSemidef := hA
  have hHH : (H*H).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self H
    rwa [hH.eq] at hh
  have hcross := posSemidef_trace_mul_nonneg hP hHH
  have hlast := auto_trace_HAHA_nonneg hP hH
  have hAeq : A=ell • (1 : Mat n)+P := by dsimp only [P]; abel
  have hcycle : Matrix.trace (H*P*H)=Matrix.trace (P*H*H) := by
    rw [Matrix.trace_mul_cycle H P H,Matrix.trace_mul_cycle H H P]
  have hexpand : Matrix.trace (A*H*A*H)=
      ell^2*Matrix.trace (H*H)+2*ell*Matrix.trace (P*H*H)+Matrix.trace (P*H*P*H) := by
    rw [hAeq]
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul]
    rw [hcycle]
    ring
  rw [hexpand,auto_trace_square_eq_frobenius H hH]
  have hmiddle : 0≤2*ell*Matrix.trace (P*H*H) := by
    have hh : 0≤Matrix.trace (P*H*H) := by simpa only [Matrix.mul_assoc] using hcross
    exact mul_nonneg (by positivity) hh
  linarith only [hmiddle,hlast]

/-- An actual spatial integration by parts, with integrability proved from compact support. -/
theorem auto_spatial_ibp {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (e : Space n) :
    (∫ x, f x*fderiv ℝ g x e)=-(∫ x, fderiv ℝ f x e*g x) := by
  have hdf : Continuous (fun x : Space n => fderiv ℝ f x e) := ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hdg : Continuous (fun x : Space n => fderiv ℝ g x e) := ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport (hcg.fderiv_apply ℝ e).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

theorem auto_partial_contDiff {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Yau.RIdx n) : ContDiff ℝ ∞ (fun x => d f x i) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem auto_partial_derivative {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Yau.RIdx n) (x : Space n) :
    d (fun y => d f y j) x i=(fderiv ℝ (fderiv ℝ f) x) (Yau.realVec i) (Yau.realVec j) := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  change (fderiv ℝ (fun y => fderiv ℝ f y (Yau.realVec j)) x) (Yau.realVec i)=_
  rw [(hd.clm_apply (hasFDerivAt_const (Yau.realVec j) x)).fderiv]
  simp

theorem auto_partial_commute {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Yau.RIdx n) (x : Space n) :
    d (fun y => d f y i) x j=d (fun y => d f y j) x i := by
  rw [auto_partial_derivative hf,auto_partial_derivative hf]
  have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by simp)
  exact h2.isSymmSndFDerivAt (by norm_num) (Yau.realVec j) (Yau.realVec i)

/-- Two genuine integrations by parts exchange the two derivative directions. -/
theorem auto_mixed_ibp_exchange {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (i j : Yau.RIdx n) :
    (∫ x, d f x i*d g x j)=(∫ x, d f x j*d g x i) := by
  have hgj := auto_partial_contDiff hg j
  have hgi := auto_partial_contDiff hg i
  have hcg_i : HasCompactSupport (fun x => d g x i) := hcg.fderiv_apply ℝ (Yau.realVec i)
  have h1 := auto_spatial_ibp hgj hf hcf (Yau.realVec i)
  have h2 := auto_spatial_ibp hf hgi hcg_i (Yau.realVec j)
  have heq (x : Space n) : d (fun y => d g y j) x i=d (fun y => d g y i) x j :=
    auto_partial_commute hg j i x
  calc
    _ = -(∫ x, f x*d (fun y => d g y j) x i) := by
      simpa only [d,mul_comm] using h1
    _ = -(∫ x, f x*d (fun y => d g y i) x j) := by
      exact congrArg Neg.neg (integral_congr_ae (ae_of_all volume fun x =>
        congrArg (fun z => f x*z) (heq x)))
    _ = _ := by
      change -(∫ x, f x*(fderiv ℝ (fun y => d g y i) x) (Yau.realVec j))=_
      rw [h2,neg_neg]
      rfl

theorem auto_second_entry_contDiff {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i j : Yau.RIdx n) :
    ContDiff ℝ ∞ (fun x => secondFDerivMatrix f x i j) :=
  (((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply contDiff_const

theorem auto_second_entry_compactSupport {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j : Yau.RIdx n) :
    HasCompactSupport (fun x => secondFDerivMatrix f x i j) := by
  have hh : HasCompactSupport (fun x => d (fun y => d f y j) x i) :=
    (hcf.fderiv_apply ℝ (Yau.realVec j)).fderiv_apply ℝ (Yau.realVec i)
  have heq : (fun x => d (fun y => d f y j) x i)=(fun x => secondFDerivMatrix f x i j) := by
    funext x
    exact auto_partial_derivative hf i j x
  rwa [heq] at hh

theorem auto_second_entry_product_integrable {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j k l : Yau.RIdx n) :
    Integrable (fun x => secondFDerivMatrix f x i j*secondFDerivMatrix f x k l) :=
  ((auto_second_entry_contDiff hf i j).continuous.mul (auto_second_entry_contDiff hf k l).continuous).integrable_of_hasCompactSupport
    (auto_second_entry_compactSupport hf hcf i j).mul_right

theorem auto_second_entry_symm {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i j : Yau.RIdx n) (x : Space n) :
    secondFDerivMatrix f x i j=secondFDerivMatrix f x j i := by
  have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by simp)
  exact h2.isSymmSndFDerivAt (by norm_num) (Yau.realVec i) (Yau.realVec j)

/-- The literal Hessian tensor identity used by the elliptic L² estimate. -/
theorem auto_hessian_integral_exchange {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j k l : Yau.RIdx n) :
    (∫ x, secondFDerivMatrix f x i j*secondFDerivMatrix f x k l)=
      (∫ x, secondFDerivMatrix f x i k*secondFDerivMatrix f x j l) := by
  have hh := auto_mixed_ibp_exchange (auto_partial_contDiff hf i) (auto_partial_contDiff hf l)
    (hcf.fderiv_apply ℝ (Yau.realVec i)) (hcf.fderiv_apply ℝ (Yau.realVec l)) j k
  have hfirst (x : Space n) : d (fun y => d f y i) x j=secondFDerivMatrix f x i j := by
    rw [auto_partial_derivative hf]
    exact auto_second_entry_symm hf j i x
  have hsecond (x : Space n) : d (fun y => d f y i) x k=secondFDerivMatrix f x i k := by
    rw [auto_partial_derivative hf]
    exact auto_second_entry_symm hf k i x
  simpa only [hfirst,hsecond,auto_partial_derivative hf,secondFDerivMatrix] using hh

theorem auto_sum4_integrable {n : ℕ}
    (g : Yau.RIdx n → Yau.RIdx n → Yau.RIdx n → Yau.RIdx n → Space n → ℝ)
    (hg : ∀ i j k l, Integrable (g i j k l)) :
    Integrable (fun x => ∑ i, ∑ j, ∑ k, ∑ l, g i j k l x) :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hg i j k l

theorem auto_integral_sum4 {n : ℕ}
    (g : Yau.RIdx n → Yau.RIdx n → Yau.RIdx n → Yau.RIdx n → Space n → ℝ)
    (hg : ∀ i j k l, Integrable (g i j k l)) :
    (∫ x, ∑ i, ∑ j, ∑ k, ∑ l, g i j k l x) = ∑ i, ∑ j, ∑ k, ∑ l, ∫ x, g i j k l x := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hg i j k l)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => hg i j k l)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hg i j k l)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_finsetSum _ fun l _ => hg i j k l

theorem auto_trace_pair_square_expansion {n : ℕ} (A H : Mat n) :
    (Matrix.trace (A*H))^2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i j*A k l)*(H j i*H l k) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,pow_two,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem auto_trace_quadratic_expansion {n : ℕ} (A H : Mat n) :
    Matrix.trace (A*H*A*H)=
      ∑ i, ∑ j, ∑ k, ∑ l, (A i j*A k l)*(H j k*H l i) := by
  have heq : A*H*A*H=(A*H)*(A*H) := by noncomm_ring
  rw [heq]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    enter [2,j]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem auto_hessian_integral_exchange_trace {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j k l : Yau.RIdx n) :
    (∫ x, secondFDerivMatrix f x j i*secondFDerivMatrix f x l k)=
      (∫ x, secondFDerivMatrix f x j k*secondFDerivMatrix f x l i) := by
  calc
    _ = ∫ x, secondFDerivMatrix f x j i*secondFDerivMatrix f x k l := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => congrArg (fun z => secondFDerivMatrix f x j i*z)
        (auto_second_entry_symm hf l k x)
    _ = ∫ x, secondFDerivMatrix f x j k*secondFDerivMatrix f x i l :=
      auto_hessian_integral_exchange hf hcf j i k l
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => congrArg (fun z => secondFDerivMatrix f x j k*z)
        (auto_second_entry_symm hf i l x)

/-- The actual compact-support constant-coefficient L² identity. No norm of the
unknown Hessian is an input to this theorem. -/
theorem auto_hessian_energy_identity {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (A : Mat n) :
    (∫ x, (Matrix.trace (A*secondFDerivMatrix f x))^2)=
      ∫ x, Matrix.trace (A*secondFDerivMatrix f x*A*secondFDerivMatrix f x) := by
  let H := secondFDerivMatrix f
  let qL := fun i j k l x => (A i j*A k l)*(H x j i*H x l k)
  let qR := fun i j k l x => (A i j*A k l)*(H x j k*H x l i)
  have hqL (i j k l : Yau.RIdx n) : Integrable (qL i j k l) :=
    (auto_second_entry_product_integrable hf hcf j i l k).const_mul (A i j*A k l)
  have hqR (i j k l : Yau.RIdx n) : Integrable (qR i j k l) :=
    (auto_second_entry_product_integrable hf hcf j k l i).const_mul (A i j*A k l)
  have hfunL : (fun x => (Matrix.trace (A*H x))^2)=
      (fun x => ∑ i, ∑ j, ∑ k, ∑ l, qL i j k l x) :=
    funext fun x => auto_trace_pair_square_expansion A (H x)
  change (∫ x, (Matrix.trace (A*H x))^2)=∫ x, Matrix.trace (A*H x*A*H x)
  rw [hfunL,auto_integral_sum4 qL hqL]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, ∫ x, qR i j k l x := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      change (∫ x, (A i j*A k l)*(secondFDerivMatrix f x j i*secondFDerivMatrix f x l k))=
        ∫ x, (A i j*A k l)*(secondFDerivMatrix f x j k*secondFDerivMatrix f x l i)
      rw [integral_const_mul,integral_const_mul,auto_hessian_integral_exchange_trace hf hcf]
    _ = ∫ x, ∑ i, ∑ j, ∑ k, ∑ l, qR i j k l x := (auto_integral_sum4 qR hqR).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => (auto_trace_quadratic_expansion A (H x)).symm

theorem auto_hessian_norm_sq_integrable {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    Integrable (fun x => ‖secondFDerivMatrix f x‖^2) := by
  have heq : (fun x => ‖secondFDerivMatrix f x‖^2)=
      (fun x => ∑ i, ∑ j, secondFDerivMatrix f x i j*secondFDerivMatrix f x i j) := by
    funext x
    rw [frobenius_norm_sq]
    simp only [pow_two]
  rw [heq]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    auto_second_entry_product_integrable hf hcf i j i j

theorem auto_hessian_quadratic_trace_integrable {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (A : Mat n) :
    Integrable (fun x => Matrix.trace (A*secondFDerivMatrix f x*A*secondFDerivMatrix f x)) := by
  have heq : (fun x => Matrix.trace (A*secondFDerivMatrix f x*A*secondFDerivMatrix f x))=
      (fun x => ∑ i, ∑ j, ∑ k, ∑ l,
        (A i j*A k l)*(secondFDerivMatrix f x j k*secondFDerivMatrix f x l i)) :=
    funext fun x => auto_trace_quadratic_expansion A _
  rw [heq]
  exact auto_sum4_integrable _ fun i j k l =>
    (auto_second_entry_product_integrable hf hcf j k l i).const_mul (A i j*A k l)

/-- The global first energy estimate: its right side is only the ACTUAL constant trace. -/
theorem auto_hessian_energy_coercive {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) {ell : ℝ} (hell : 0≤ell)
    (A : Mat n) (hA : (A-ell • (1 : Mat n)).PosSemidef) :
    ell^2*(∫ x, ‖secondFDerivMatrix f x‖^2)≤∫ x, (Matrix.trace (A*secondFDerivMatrix f x))^2 := by
  have hsym (x : Space n) : (secondFDerivMatrix f x).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using auto_second_entry_symm hf j i x
  have hi := integral_mono ((auto_hessian_norm_sq_integrable hf hcf).const_mul (ell^2))
    (auto_hessian_quadratic_trace_integrable hf hcf A)
    (fun x => auto_elliptic_trace_hessian_sq hell A _ hA (hsym x))
  rw [integral_const_mul,← auto_hessian_energy_identity hf hcf A] at hi
  exact hi

end Yau.LeafProofs.L05AutonomousAux
