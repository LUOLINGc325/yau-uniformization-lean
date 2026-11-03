import Yau.LeafProofs.L05AutonomousHessianEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

local instance autoCutoffEnergy_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoCutoffEnergy_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

def autoEnergyForm {n : ℕ} (A : Mat n) (v w : Yau.RIdx n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*v i*w j

def autoEnergyGradientSq {n : ℕ} (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, (d f x i)^2

theorem autoEnergyGradientSq_norm {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ f x‖^2=autoEnergyGradientSq f x := by
  simpa only [autoEnergyGradientSq,d,complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).norm_dual (fderiv ℝ f x)

theorem autoEnergyForm_dotProduct {n : ℕ} (A : Mat n) (v w : Yau.RIdx n → ℝ) :
    v ⬝ᵥ (A *ᵥ w)=autoEnergyForm A v w := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,autoEnergyForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Quadratic ellipticity gives the genuine sharp principal bilinear budget L. -/
theorem auto_slope_bilinear_bound {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) (v w : Yau.RIdx n → ℝ) :
    |autoEnergyForm (A : Mat n) v w|≤
      L*Real.sqrt (∑ i, (v i)^2)*Real.sqrt (∑ i, (w i)^2) := by
  have hquad (p : Yau.RIdx n → ℝ) : ell*(∑ i, (p i)^2)≤autoEnergyForm (A : Mat n) p p ∧
      autoEnergyForm (A : Mat n) p p≤L*(∑ i, (p i)^2) := auto_slope_quadratic_bounds hA p
  have hcs := (slopeSet_posDef hell hA).star_dotProduct_mulVec_mul_le v w
  simp only [star_trivial,autoEnergyForm_dotProduct] at hcs
  have hP : 0≤autoEnergyForm (A : Mat n) v v :=
    (mul_nonneg hell.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hquad v).1
  have hQ : 0≤autoEnergyForm (A : Mat n) w w :=
    (mul_nonneg hell.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hquad w).1
  have hLp : 0≤L*(∑ i, (v i)^2) :=
    mul_nonneg (hell.le.trans hL) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hprod := mul_le_mul (hquad v).2 (hquad w).2 hQ hLp
  have hsV := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))
  have hsW := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (w i))
  have hnonneg : 0≤L*Real.sqrt (∑ i, (v i)^2)*Real.sqrt (∑ i, (w i)^2) := by
    apply mul_nonneg
    · exact mul_nonneg (hell.le.trans hL) (Real.sqrt_nonneg _)
    · exact Real.sqrt_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
  rw [sq_abs]
  calc
    _ ≤ autoEnergyForm (A : Mat n) v v*autoEnergyForm (A : Mat n) w w := by
      simpa only [pow_two] using hcs
    _ ≤ _ := hprod
    _ = _ := by rw [mul_pow,mul_pow,hsV,hsW]; ring

theorem auto_partial_mul {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Yau.RIdx n) (x : Space n) :
    d (fun y => f y*g y) x i=d f x i*g x+f x*d g x i := by
  unfold d
  change (fderiv ℝ (f*g) x) (Yau.realVec i)=_
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

theorem auto_partial_sq {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Yau.RIdx n) (x : Space n) :
    d (fun y => (f y)^2) x i=2*f x*d f x i := by
  have hh := auto_partial_mul hf hf i x
  simpa only [← pow_two] using hh.trans (by ring)

theorem auto_partial_cutoff_flux {n : ℕ} {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (i j : Yau.RIdx n) (x : Space n) :
    d (fun y => (eta y)^2*d f y j) x i=
      2*eta x*d eta x i*d f x j+(eta x)^2*secondFDerivMatrix f x i j := by
  rw [auto_partial_mul (heta.pow 2) (auto_partial_contDiff hf j),auto_partial_sq heta,
    auto_partial_derivative hf]
  rfl

theorem auto_cutoff_sq_compact {n : ℕ} {eta : Space n → ℝ}
    (hc : HasCompactSupport eta) : HasCompactSupport (fun x => (eta x)^2) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun x hx => by simp only [Pi.zero_apply,hx,zero_pow (by norm_num : 2≠0)]

theorem auto_cutoff_sq_integrable {n : ℕ} {eta g : Space n → ℝ}
    (heta : Continuous eta) (hc : HasCompactSupport eta) (hg : Continuous g) :
    Integrable (fun x => (eta x)^2*g x) :=
  ((heta.pow 2).mul hg).integrable_of_hasCompactSupport (auto_cutoff_sq_compact hc).mul_right

theorem auto_integral_sum2 {n : ℕ} (g : Yau.RIdx n → Yau.RIdx n → Space n → ℝ)
    (hg : ∀ i j, Integrable (g i j)) :
    (∫ x, ∑ i, ∑ j, g i j x)=∑ i, ∑ j, ∫ x, g i j x := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hg i j)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ fun j _ => hg i j

theorem auto_energy_trace_eq {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (A : Mat n) (x : Space n) :
    Matrix.trace (A*secondFDerivMatrix f x)=∑ i, ∑ j, A i j*secondFDerivMatrix f x i j := by
  change (∑ i, ∑ j, A i j*secondFDerivMatrix f x j i)=_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [auto_second_entry_symm hf j i]

/-- Each tensor entry comes from the actual compactly supported flux eta² partial_j f. -/
theorem auto_cutoff_entry_ibp {n : ℕ} {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta)
    (i j : Yau.RIdx n) :
    (∫ x, (eta x)^2*d f x i*d f x j)=
      -(∫ x, (eta x)^2*f x*secondFDerivMatrix f x i j)
      -2*(∫ x, eta x*f x*d eta x i*d f x j) := by
  have hflux := auto_spatial_ibp hf ((heta.pow 2).mul (auto_partial_contDiff hf j))
    ((auto_cutoff_sq_compact hceta).mul_right) (Yau.realVec i)
  have h1 : Integrable (fun x => (eta x)^2*f x*secondFDerivMatrix f x i j) := by
    simpa only [mul_assoc,Pi.mul_apply] using auto_cutoff_sq_integrable heta.continuous hceta
      (hf.continuous.mul (auto_second_entry_contDiff hf i j).continuous)
  have h2 : Integrable (fun x => eta x*f x*d eta x i*d f x j) := by
    exact (((heta.continuous.mul hf.continuous).mul (auto_partial_contDiff heta i).continuous).mul
      (auto_partial_contDiff hf j).continuous).integrable_of_hasCompactSupport
      ((hceta.mul_right).mul_right).mul_right
  have hl : (fun x => f x*d (fun y => (eta y)^2*d f y j) x i)=
      (fun x => (eta x)^2*f x*secondFDerivMatrix f x i j+
        2*(eta x*f x*d eta x i*d f x j)) := by
    funext x
    rw [auto_partial_cutoff_flux hf heta]
    ring
  have hr : (fun x => d f x i*((eta x)^2*d f x j))=
      (fun x => (eta x)^2*d f x i*d f x j) := by funext x; ring
  change (∫ x, f x*d (fun y => (eta y)^2*d f y j) x i)=
    -(∫ x, d f x i*((eta x)^2*d f x j)) at hflux
  rw [hl,hr,integral_add h1 (h2.const_mul 2),integral_const_mul] at hflux
  linarith only [hflux]

theorem autoEnergyForm_continuous {n : ℕ} (A : Mat n) {v w : Space n → Yau.RIdx n → ℝ}
    (hv : ∀ i, Continuous (fun x => v x i)) (hw : ∀ i, Continuous (fun x => w x i)) :
    Continuous (fun x => autoEnergyForm A (v x) (w x)) := by
  unfold autoEnergyForm
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_const.mul (hv i)).mul (hw j)

theorem auto_integral_form_weight {n : ℕ} (A : Mat n) {h : Space n → ℝ}
    {v w : Space n → Yau.RIdx n → ℝ} (hh : Continuous h) (hch : HasCompactSupport h)
    (hv : ∀ i, Continuous (fun x => v x i)) (hw : ∀ i, Continuous (fun x => w x i)) :
    (∫ x, h x*autoEnergyForm A (v x) (w x))=
      ∑ i, ∑ j, A i j*(∫ x, h x*v x i*w x j) := by
  have hint (i j : Yau.RIdx n) : Integrable (fun x => h x*v x i*w x j) :=
    ((hh.mul (hv i)).mul (hw j)).integrable_of_hasCompactSupport (hch.mul_right).mul_right
  have heq : (fun x => h x*autoEnergyForm A (v x) (w x))=
      (fun x => ∑ i, ∑ j, A i j*(h x*v x i*w x j)) := by
    funext x
    simp only [autoEnergyForm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq,auto_integral_sum2 _ (fun i j => (hint i j).const_mul (A i j))]
  simp only [integral_const_mul]

theorem auto_integral_trace_weight {n : ℕ} (A : Mat n) {f h : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : Continuous h) (hch : HasCompactSupport h) :
    (∫ x, h x*Matrix.trace (A*secondFDerivMatrix f x))=
      ∑ i, ∑ j, A i j*(∫ x, h x*secondFDerivMatrix f x i j) := by
  have hint (i j : Yau.RIdx n) : Integrable (fun x => h x*secondFDerivMatrix f x i j) :=
    (hh.mul (auto_second_entry_contDiff hf i j).continuous).integrable_of_hasCompactSupport hch.mul_right
  have heq : (fun x => h x*Matrix.trace (A*secondFDerivMatrix f x))=
      (fun x => ∑ i, ∑ j, A i j*(h x*secondFDerivMatrix f x i j)) := by
    funext x
    rw [auto_energy_trace_eq hf]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq,auto_integral_sum2 _ (fun i j => (hint i j).const_mul (A i j))]
  simp only [integral_const_mul]

/-- The cutoff energy identity has no compact-support requirement on the unknown f. -/
theorem auto_cutoff_gradient_identity {n : ℕ} {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta) (A : Mat n) :
    (∫ x, (eta x)^2*autoEnergyForm A (d f x) (d f x))=
      -(∫ x, (eta x)^2*f x*Matrix.trace (A*secondFDerivMatrix f x))
      -2*(∫ x, eta x*f x*autoEnergyForm A (d eta x) (d f x)) := by
  have hdf (i : Yau.RIdx n) := (auto_partial_contDiff hf i).continuous
  have hde (i : Yau.RIdx n) := (auto_partial_contDiff heta i).continuous
  have hs : Continuous (fun x => (eta x)^2) := heta.continuous.pow 2
  have hsf : Continuous (fun x => (eta x)^2*f x) := hs.mul hf.continuous
  have hef : Continuous (fun x => eta x*f x) := heta.continuous.mul hf.continuous
  rw [auto_integral_form_weight A hs (auto_cutoff_sq_compact hceta) hdf hdf,
    auto_integral_trace_weight A hf hsf (auto_cutoff_sq_compact hceta).mul_right,
    auto_integral_form_weight A hef hceta.mul_right hde hdf]
  simp_rw [auto_cutoff_entry_ibp hf heta hceta]
  simp only [mul_sub,mul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib,Finset.mul_sum]
  congr 1
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem autoEnergyGradientSq_nonneg {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    0≤autoEnergyGradientSq f x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem autoEnergyGradientSq_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (autoEnergyGradientSq f) :=
  continuous_finsetSum _ fun i _ => (auto_partial_contDiff hf i).continuous.pow 2

theorem autoEnergyGradientSq_compact {n : ℕ} {eta : Space n → ℝ} (hceta : HasCompactSupport eta) :
    HasCompactSupport (autoEnergyGradientSq eta) := by
  unfold autoEnergyGradientSq
  convert (HasCompactSupport.finset_sum (s := Finset.univ)
    fun i _ => auto_cutoff_sq_compact (hceta.fderiv_apply ℝ (Yau.realVec i))) using 1
  funext x
  simp only [Finset.sum_apply,d]

theorem auto_energy_trace_continuous {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (A : Mat n) :
    Continuous (fun x => Matrix.trace (A*secondFDerivMatrix f x)) := by
  have heq := funext (auto_energy_trace_eq hf A)
  rw [heq]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (auto_second_entry_contDiff hf i j).continuous

/-- Scalar Young absorption with the elliptic coefficient exposed. -/
theorem auto_cutoff_young {ell L a b X Y : ℝ} (hell : 0<ell) (hX : 0≤X) (hY : 0≤Y) :
    2*|a| *|b| *L*Real.sqrt X*Real.sqrt Y≤
      ell/2*a^2*Y+(2*L^2/ell)*b^2*X := by
  calc
    _ = 2*(|a| *Real.sqrt Y)*(L*|b| *Real.sqrt X) := by ring
    _ ≤ (ell/2)*(|a| *Real.sqrt Y)^2+(ell/2)⁻¹*(L*|b| *Real.sqrt X)^2 :=
      two_mul_le_add_mul_sq (half_pos hell)
    _ = _ := by
      simp only [mul_pow,sq_abs,Real.sq_sqrt hX,Real.sq_sqrt hY]
      field_simp

/-- The actual drift-free cutoff cross term is absorbed by half the principal energy. -/
theorem auto_cutoff_cross_bound {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) (f eta : Space n → ℝ) (x : Space n) :
    2*|eta x*f x*autoEnergyForm (A : Mat n) (d eta x) (d f x)|≤
      ell/2*(eta x)^2*autoEnergyGradientSq f x+
        (2*L^2/ell)*(f x)^2*autoEnergyGradientSq eta x := by
  have hb := auto_slope_bilinear_bound hell hL hA (d eta x) (d f x)
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0≤2*|eta x| *|f x|)
  simp only [abs_mul] at ⊢
  calc
    _ ≤ 2*|eta x| *|f x| *(L*Real.sqrt (autoEnergyGradientSq eta x)*
        Real.sqrt (autoEnergyGradientSq f x)) := by
      simpa only [autoEnergyGradientSq,mul_assoc] using hh
    _ = 2*|eta x| *|f x| *L*Real.sqrt (autoEnergyGradientSq eta x)*
        Real.sqrt (autoEnergyGradientSq f x) := by ring
    _ ≤ _ := auto_cutoff_young hell (autoEnergyGradientSq_nonneg eta x)
      (autoEnergyGradientSq_nonneg f x)

/-- A genuine localized gradient estimate, absorbing the cutoff cross term internally. -/
theorem auto_cutoff_gradient_energy {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta) :
    ell*(∫ x, (eta x)^2*autoEnergyGradientSq f x)≤
      2*(∫ x, |(eta x)^2*f x*Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)|)+
        (4*L^2/ell)*(∫ x, (f x)^2*autoEnergyGradientSq eta x) := by
  have hG := auto_cutoff_sq_integrable heta.continuous hceta (autoEnergyGradientSq_continuous hf)
  have hF : Continuous (fun x => autoEnergyForm (A : Mat n) (d f x) (d f x)) :=
    autoEnergyForm_continuous _ (fun i => (auto_partial_contDiff hf i).continuous)
      (fun i => (auto_partial_contDiff hf i).continuous)
  have hP := auto_cutoff_sq_integrable heta.continuous hceta hF
  have hS : Integrable (fun x => (eta x)^2*f x*Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)) := by
    simpa only [mul_assoc,Pi.mul_apply] using auto_cutoff_sq_integrable heta.continuous hceta
      (hf.continuous.mul (auto_energy_trace_continuous hf _))
  have hC : Integrable (fun x => eta x*f x*autoEnergyForm (A : Mat n) (d eta x) (d f x)) :=
    ((heta.continuous.mul hf.continuous).mul (autoEnergyForm_continuous _
      (fun i => (auto_partial_contDiff heta i).continuous)
      (fun i => (auto_partial_contDiff hf i).continuous))).integrable_of_hasCompactSupport
        (hceta.mul_right).mul_right
  have hE : Integrable (fun x => (f x)^2*autoEnergyGradientSq eta x) :=
    ((hf.continuous.pow 2).mul (autoEnergyGradientSq_continuous heta)).integrable_of_hasCompactSupport
      (autoEnergyGradientSq_compact hceta).mul_left
  have hlow := integral_mono (hG.const_mul ell) hP (fun x => by
    have hh := mul_le_mul_of_nonneg_left (auto_slope_quadratic_bounds hA (d f x)).1 (sq_nonneg (eta x))
    simpa only [autoEnergyGradientSq,autoEnergyForm,mul_assoc,mul_comm ell] using hh)
  rw [integral_const_mul] at hlow
  have hsrc : -(∫ x, (eta x)^2*f x*Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))≤
      ∫ x, |(eta x)^2*f x*Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)| :=
    (neg_le_abs _).trans abs_integral_le_integral_abs
  have hcross := integral_mono ((hC.abs).const_mul 2)
    ((hG.const_mul (ell/2)).add (hE.const_mul (2*L^2/ell)))
    (fun x => by simpa only [Pi.add_apply,mul_assoc] using auto_cutoff_cross_bound hell hL hA f eta x)
  simp only [Pi.add_apply] at hcross
  rw [integral_const_mul,integral_add (hG.const_mul (ell/2)) (hE.const_mul (2*L^2/ell)),
    integral_const_mul,integral_const_mul] at hcross
  have hcabs : -(∫ x, eta x*f x*autoEnergyForm (A : Mat n) (d eta x) (d f x))≤
      ∫ x, |eta x*f x*autoEnergyForm (A : Mat n) (d eta x) (d f x)| :=
    (neg_le_abs _).trans abs_integral_le_integral_abs
  have hid := auto_cutoff_gradient_identity hf heta hceta (A : Mat n)
  linear_combination 2*hlow+2*hsrc+2*hcross+4*hcabs+2*hid

theorem auto_partial_add {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Yau.RIdx n) (x : Space n) :
    d (fun y => f y+g y) x i=d f x i+d g x i := by
  unfold d
  change (fderiv ℝ (f+g) x) (Yau.realVec i)=_
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem auto_second_mul {n : ℕ} {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (i j : Yau.RIdx n) (x : Space n) :
    secondFDerivMatrix (fun y => eta y*f y) x i j=
      eta x*secondFDerivMatrix f x i j+f x*secondFDerivMatrix eta x i j+
        d eta x i*d f x j+d eta x j*d f x i := by
  have hj : (fun y => d (fun z => eta z*f z) y j)=
      (fun y => d eta y j*f y+eta y*d f y j) := funext fun y => auto_partial_mul heta hf j y
  have he : d (fun y => d (fun z => eta z*f z) y j) x i=
      secondFDerivMatrix (fun z => eta z*f z) x i j := auto_partial_derivative (heta.mul hf) i j x
  rw [← he,hj]
  rw [auto_partial_add ((auto_partial_contDiff heta j).mul hf)
    (heta.mul (auto_partial_contDiff hf j)),
    auto_partial_mul (auto_partial_contDiff heta j) hf,
    auto_partial_mul heta (auto_partial_contDiff hf j),
    auto_partial_derivative heta,auto_partial_derivative hf]
  unfold secondFDerivMatrix
  ring

theorem autoEnergyForm_commute {n : ℕ} (A : Mat n) (hA : A.IsHermitian) (v w : Yau.RIdx n → ℝ) :
    autoEnergyForm A v w=autoEnergyForm A w v := by
  unfold autoEnergyForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh : A j i=A i j := by simpa only [star_trivial] using hA.apply i j
  rw [hh]
  ring

/-- Exact constant-coefficient contraction of the actual cutoff Hessian. -/
theorem auto_cutoff_trace {n : ℕ} {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (A : Mat n) (hA : A.IsHermitian) (x : Space n) :
    Matrix.trace (A*secondFDerivMatrix (fun y => eta y*f y) x)=
      eta x*Matrix.trace (A*secondFDerivMatrix f x)+
      2*autoEnergyForm A (d eta x) (d f x)+f x*Matrix.trace (A*secondFDerivMatrix eta x) := by
  have hex : Matrix.trace (A*secondFDerivMatrix (fun y => eta y*f y) x)=
      eta x*Matrix.trace (A*secondFDerivMatrix f x)+
      f x*Matrix.trace (A*secondFDerivMatrix eta x)+
      autoEnergyForm A (d eta x) (d f x)+autoEnergyForm A (d f x) (d eta x) := by
    rw [auto_energy_trace_eq (heta.mul hf),auto_energy_trace_eq hf,auto_energy_trace_eq heta]
    simp_rw [auto_second_mul hf heta]
    simp only [autoEnergyForm,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hex,autoEnergyForm_commute A hA (d f x) (d eta x)]
  ring

theorem auto_slope_bilinear_square {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) (v w : Yau.RIdx n → ℝ) :
    (autoEnergyForm (A : Mat n) v w)^2≤L^2*(∑ i, (v i)^2)*(∑ i, (w i)^2) := by
  have hbound := auto_slope_bilinear_bound hell hL hA v w
  have hn : 0≤L*Real.sqrt (∑ i, (v i)^2)*Real.sqrt (∑ i, (w i)^2) := by
    exact mul_nonneg (mul_nonneg (hell.le.trans hL) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hh := (sq_le_sq₀ (abs_nonneg _) hn).mpr hbound
  simpa only [sq_abs,mul_pow,Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i)),
    Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (w i))] using hh

theorem auto_energy_trace_compact {n : ℕ} {eta : Space n → ℝ}
    (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta) (A : Mat n) :
    HasCompactSupport (fun x => Matrix.trace (A*secondFDerivMatrix eta x)) := by
  have hi (i j : Yau.RIdx n) : HasCompactSupport (fun x => A i j*secondFDerivMatrix eta x i j) :=
    (auto_second_entry_compactSupport heta hceta i j).mul_left
  convert (HasCompactSupport.finset_sum (s := Finset.univ) fun i _ =>
    HasCompactSupport.finset_sum (s := Finset.univ) fun j _ => hi i j) using 1
  funext x
  simp only [Finset.sum_apply]
  exact auto_energy_trace_eq heta A x

/-- The cutoff trace square is controlled using only the actual first gradient and trace. -/
theorem auto_cutoff_trace_square_bound {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (x : Space n) :
    (Matrix.trace ((A : Mat n)*secondFDerivMatrix (fun y => eta y*f y) x))^2≤
      3*(eta x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2+
      12*L^2*autoEnergyGradientSq eta x*autoEnergyGradientSq f x+
      3*(f x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix eta x))^2 := by
  rw [auto_cutoff_trace hf heta _ A.property]
  have hb := auto_slope_bilinear_square hell hL hA (d eta x) (d f x)
  change (autoEnergyForm (A : Mat n) (d eta x) (d f x))^2≤
    L^2*autoEnergyGradientSq eta x*autoEnergyGradientSq f x at hb
  have hthree (a b c : ℝ) : (a+b+c)^2≤3*a^2+3*b^2+3*c^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hh := hthree (eta x*Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))
    (2*autoEnergyForm (A : Mat n) (d eta x) (d f x))
    (f x*Matrix.trace ((A : Mat n)*secondFDerivMatrix eta x))
  nlinarith only [hh,hb]

/-- Localized L² coercivity with every cutoff error explicit and genuinely integrable. -/
theorem auto_cutoff_hessian_energy {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta) :
    ell^2*(∫ x, ‖secondFDerivMatrix (fun y => eta y*f y) x‖^2)≤
      3*(∫ x, (eta x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2)+
      12*L^2*(∫ x, autoEnergyGradientSq eta x*autoEnergyGradientSq f x)+
      3*(∫ x, (f x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix eta x))^2) := by
  have h1 : Integrable (fun x => (eta x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2) :=
    auto_cutoff_sq_integrable heta.continuous hceta ((auto_energy_trace_continuous hf (A : Mat n)).pow 2)
  have h2 : Integrable (fun x => autoEnergyGradientSq eta x*autoEnergyGradientSq f x) :=
    ((autoEnergyGradientSq_continuous heta).mul (autoEnergyGradientSq_continuous hf)).integrable_of_hasCompactSupport
      (autoEnergyGradientSq_compact hceta).mul_right
  have h3 : Integrable (fun x => (f x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix eta x))^2) :=
    ((hf.continuous.pow 2).mul ((auto_energy_trace_continuous heta _).pow 2)).integrable_of_hasCompactSupport
      (auto_cutoff_sq_compact (auto_energy_trace_compact heta hceta _)).mul_left
  have hleft : Integrable (fun x => (Matrix.trace ((A : Mat n)*secondFDerivMatrix (fun y => eta y*f y) x))^2) := by
    exact (auto_energy_trace_continuous (heta.mul hf) _).pow 2 |>.integrable_of_hasCompactSupport
      (auto_cutoff_sq_compact (auto_energy_trace_compact (heta.mul hf) hceta.mul_right _))
  have hm := integral_mono hleft (((h1.const_mul 3).add (h2.const_mul (12*L^2))).add (h3.const_mul 3))
    (fun x => by simpa only [Pi.add_apply,mul_assoc] using auto_cutoff_trace_square_bound hell hL hA hf heta x)
  simp only [Pi.add_apply] at hm
  have h12 : Integrable (fun x => 3*((eta x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2)+
      12*L^2*(autoEnergyGradientSq eta x*autoEnergyGradientSq f x)) := by
    convert ((h1.const_mul 3).add (h2.const_mul (12*L^2))) using 1
  rw [integral_add h12 (h3.const_mul 3),
    integral_add (h1.const_mul 3) (h2.const_mul (12*L^2)),integral_const_mul,integral_const_mul,
    integral_const_mul] at hm
  exact (auto_hessian_energy_coercive (heta.mul hf) hceta.mul_right hell.le _ hA.1).trans hm

end Yau.LeafProofs.L05AutonomousAux
