import Yau.LeafProofs.L05AutonomousCutoffEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius MatrixOrder
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

local instance autoLocalEnergy_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoLocalEnergy_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

theorem auto_gradientSq_support_subset {n : ℕ} (eta : Space n → ℝ) :
    Function.support (autoEnergyGradientSq eta)⊆tsupport eta := by
  intro x hx
  by_contra hxt
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt
  have hzero : autoEnergyGradientSq eta x=0 := by simp only [autoEnergyGradientSq,d,hz]; simp
  exact hx hzero

theorem auto_hessian_zero_off_tsupport {n : ℕ} {eta : Space n → ℝ} {x : Space n}
    (hx : x∉tsupport eta) : secondFDerivMatrix eta x=0 := by
  have hx' : x∉tsupport (fderiv ℝ eta) := fun hh => hx (tsupport_fderiv_subset ℝ hh)
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx'
  ext i j
  simp only [secondFDerivMatrix,hz,_root_.zero_apply,Matrix.zero_apply]

theorem auto_hessian_sq_continuous {n : ℕ} {eta : Space n → ℝ} (heta : ContDiff ℝ ∞ eta) :
    Continuous (fun x => ‖secondFDerivMatrix eta x‖^2) := by
  have heq : (fun x => ‖secondFDerivMatrix eta x‖^2)=
      (fun x => ∑ i, ∑ j, (secondFDerivMatrix eta x i j)^2) := by
    funext x
    rw [frobenius_norm_sq]
  rw [heq]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (auto_second_entry_contDiff heta i j).continuous.pow 2

theorem auto_hessian_sq_support_subset {n : ℕ} (eta : Space n → ℝ) :
    Function.support (fun x => ‖secondFDerivMatrix eta x‖^2)⊆tsupport eta := by
  intro x hx
  by_contra hxt
  exact hx (by change ‖secondFDerivMatrix eta x‖^2=0; rw [auto_hessian_zero_off_tsupport hxt,norm_zero]; norm_num)

/-- The only supremum chosen here concerns a fixed, smooth compact cutoff. -/
theorem auto_compact_cutoff_gradient_bound {n : ℕ} {eta : Space n → ℝ}
    (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta) :
    ∃ D : ℝ, 0<D ∧ ∀ x, autoEnergyGradientSq eta x≤D^2 := by
  have hc : HasCompactSupport (fderiv ℝ eta) := hceta.fderiv ℝ
  have hcont := (heta.fderiv_right (m := ∞) (by simp)).continuous
  obtain ⟨D,hD⟩ := hc.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨1+|D|,by positivity,?_⟩
  intro x
  rw [← autoEnergyGradientSq_norm]
  have hb : ‖fderiv ℝ eta x‖≤1+|D| := by
    by_cases hx : x∈tsupport (fderiv ℝ eta)
    · exact (hD x hx).trans (by linarith [le_abs_self D])
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
      positivity
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb

/-- A compact nonnegative weight uses function bounds only on its genuine support. -/
theorem auto_weighted_square_bound {n : ℕ} {w f : Space n → ℝ} {S : Set (Space n)} {M : ℝ}
    (hw : Continuous w) (hcw : HasCompactSupport w) (hw0 : ∀ x, 0≤w x)
    (hws : Function.support w⊆S) (hf : Continuous f) (hM : 0≤M) (hMf : ∀ x∈S, |f x|≤M) :
    (∫ x, w x*(f x)^2)≤M^2*(∫ x, w x) := by
  have hint : Integrable (fun x => w x*(f x)^2) := (hw.mul (hf.pow 2)).integrable_of_hasCompactSupport hcw.mul_right
  have hwi : Integrable w := hw.integrable_of_hasCompactSupport hcw
  have hm := integral_mono hint (hwi.const_mul (M^2)) (fun x => by
    by_cases hx : w x=0
    · simp [hx]
    · have hs := hMf x (hws hx)
      have hh := (sq_le_sq₀ (abs_nonneg _) hM).mpr hs
      rw [sq_abs] at hh
      nlinarith only [mul_le_mul_of_nonneg_left hh (hw0 x)])
  rwa [integral_const_mul] at hm

theorem auto_weighted_abs_product_bound {n : ℕ} {w f g : Space n → ℝ} {S : Set (Space n)} {M B : ℝ}
    (hw : Continuous w) (hcw : HasCompactSupport w) (hw0 : ∀ x, 0≤w x)
    (hws : Function.support w⊆S) (hf : Continuous f) (hg : Continuous g)
    (hM : 0≤M) (_hB : 0≤B) (hMf : ∀ x∈S, |f x|≤M) (hBg : ∀ x∈S, |g x|≤B) :
    (∫ x, |w x*f x*g x|)≤M*B*(∫ x, w x) := by
  have hint : Integrable (fun x => |w x*f x*g x|) := (((hw.mul hf).mul hg).integrable_of_hasCompactSupport (hcw.mul_right).mul_right).abs
  have hwi : Integrable w := hw.integrable_of_hasCompactSupport hcw
  have hm := integral_mono hint (hwi.const_mul (M*B)) (fun x => by
    by_cases hx : w x=0
    · simp [hx]
    · have hxf := hMf x (hws hx)
      have hxg := hBg x (hws hx)
      rw [abs_mul,abs_mul,abs_of_nonneg (hw0 x)]
      have hh := mul_le_mul hxf hxg (abs_nonneg _) hM
      nlinarith only [mul_le_mul_of_nonneg_left hh (hw0 x)])
  rwa [integral_const_mul] at hm

/-- Trace and value bounds give a local first-gradient L² bound; no gradient bound is assumed. -/
theorem auto_bounded_cutoff_gradient {n : ℕ} {ell L M B : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) {f eta : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (heta : ContDiff ℝ ∞ eta) (hceta : HasCompactSupport eta)
    {S : Set (Space n)} (hs : tsupport eta⊆S) (hM : 0≤M) (hB : 0≤B)
    (hMf : ∀ x∈S, |f x|≤M)
    (hBt : ∀ x∈S, |Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)|≤B) :
    ell*(∫ x, (eta x)^2*autoEnergyGradientSq f x)≤
      2*M*B*(∫ x, (eta x)^2)+(4*L^2/ell)*M^2*(∫ x, autoEnergyGradientSq eta x) := by
  have hs2 : Function.support (fun x => (eta x)^2)⊆S := by
    intro x hx
    apply hs
    apply subset_closure
    intro hz
    exact hx (by change (eta x)^2=0; rw [hz]; norm_num)
  have hsrc := auto_weighted_abs_product_bound (w := fun x => (eta x)^2) (heta.continuous.pow 2) (auto_cutoff_sq_compact hceta)
    (fun x => sq_nonneg (eta x)) hs2 hf.continuous (auto_energy_trace_continuous hf _) hM hB hMf hBt
  have hg := auto_weighted_square_bound (autoEnergyGradientSq_continuous heta)
    (autoEnergyGradientSq_compact hceta) (autoEnergyGradientSq_nonneg eta)
    ((auto_gradientSq_support_subset eta).trans hs) hf.continuous hM hMf
  have he := auto_cutoff_gradient_energy hell hL hA hf heta hceta
  have heq : (∫ x, (f x)^2*autoEnergyGradientSq eta x)=∫ x, autoEnergyGradientSq eta x*(f x)^2 := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => mul_comm _ _
  rw [heq] at he
  have hfac : 0≤4*L^2/ell := div_nonneg (by positivity) hell.le
  nlinarith only [he,hsrc,mul_le_mul_of_nonneg_left hg hfac]

theorem auto_hessian_sq_compact {n : ℕ} {eta : Space n → ℝ} (hceta : HasCompactSupport eta) :
    HasCompactSupport (fun x => ‖secondFDerivMatrix eta x‖^2) :=
  hceta.mono' (auto_hessian_sq_support_subset eta)

/-- Fixed nested cutoffs produce a budget before the matrix and the candidate function. -/
theorem auto_nested_cutoff_hessian_bound {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {eta₁ eta₂ : Space n → ℝ} (he₁ : ContDiff ℝ ∞ eta₁) (he₂ : ContDiff ℝ ∞ eta₂)
    (hc₁ : HasCompactSupport eta₁) (hc₂ : HasCompactSupport eta₂)
    {S : Set (Space n)} (hs₁ : tsupport eta₁⊆S) (hs₂ : tsupport eta₂⊆S)
    (hcover : ∀ x∈tsupport eta₂, eta₁ x=1) :
    ∃ C : ℝ, 0<C ∧ ∀ A : Sym n, A∈slopeSet n ell L →
      ∀ M B : ℝ, 0≤M → 0≤B → ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      (∀ x∈S, |f x|≤M) →
      (∀ x∈S, |Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)|≤B) →
      (∫ x, ‖secondFDerivMatrix (fun y => eta₂ y*f y) x‖^2)≤C*(M^2+B^2) := by
  obtain ⟨D,hD,hDb⟩ := auto_compact_cutoff_gradient_bound he₂ hc₂
  let I₁ := ∫ x, (eta₁ x)^2
  let I₂ := ∫ x, (eta₂ x)^2
  let J₁ := ∫ x, autoEnergyGradientSq eta₁ x
  let J₂ := ∫ x, ‖secondFDerivMatrix eta₂ x‖^2
  let K := Real.sqrt (Fintype.card (Yau.RIdx n))*((2*n : ℝ)*L)
  let G := (I₁+(4*L^2/ell)*J₁)/ell
  let E := 3*I₂+12*L^2*D^2*G+3*K^2*J₂
  have hI₁ : 0≤I₁ := integral_nonneg fun x => sq_nonneg _
  have hI₂ : 0≤I₂ := integral_nonneg fun x => sq_nonneg _
  have hJ₁ : 0≤J₁ := integral_nonneg (autoEnergyGradientSq_nonneg eta₁)
  have hJ₂ : 0≤J₂ := integral_nonneg fun x => sq_nonneg _
  have hG : 0≤G := div_nonneg (add_nonneg hI₁ (mul_nonneg (by positivity) hJ₁)) hell.le
  have hE : 0≤E := by dsimp only [E]; positivity
  refine ⟨1+E/ell^2,by positivity,?_⟩
  intro A hA M B hM hB f hf hMf hBt
  let W := M^2+B^2
  have hW : 0≤W := add_nonneg (sq_nonneg M) (sq_nonneg B)
  have hMW : M^2≤W := le_add_of_nonneg_right (sq_nonneg B)
  have hBW : B^2≤W := le_add_of_nonneg_left (sq_nonneg M)
  have hMB : 2*M*B≤W := by dsimp only [W]; nlinarith only [sq_nonneg (M-B)]
  have hgrad : (∫ x, (eta₁ x)^2*autoEnergyGradientSq f x)≤G*W := by
    have hh := auto_bounded_cutoff_gradient hell hL hA hf he₁ hc₁ hs₁ hM hB hMf hBt
    have hfirst := mul_le_mul_of_nonneg_right hMB hI₁
    have hsecond := mul_le_mul_of_nonneg_right hMW (mul_nonneg (by positivity : 0≤4*L^2/ell) hJ₁)
    have hbound : ell*(∫ x, (eta₁ x)^2*autoEnergyGradientSq f x)≤
        (I₁+(4*L^2/ell)*J₁)*W := by
      change ell*(∫ x, (eta₁ x)^2*autoEnergyGradientSq f x)≤2*M*B*I₁+(4*L^2/ell)*M^2*J₁ at hh
      nlinarith only [hh,hfirst,hsecond]
    dsimp only [G]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hell).mpr
    simpa only [mul_comm ell] using hbound
  have hi₁ : Integrable (fun x => (eta₁ x)^2*autoEnergyGradientSq f x) :=
    auto_cutoff_sq_integrable he₁.continuous hc₁ (autoEnergyGradientSq_continuous hf)
  have hi₂ : Integrable (fun x => autoEnergyGradientSq eta₂ x*autoEnergyGradientSq f x) :=
    ((autoEnergyGradientSq_continuous he₂).mul (autoEnergyGradientSq_continuous hf)).integrable_of_hasCompactSupport
      (autoEnergyGradientSq_compact hc₂).mul_right
  have hcross : (∫ x, autoEnergyGradientSq eta₂ x*autoEnergyGradientSq f x)≤D^2*G*W := by
    have hh := integral_mono hi₂ (hi₁.const_mul (D^2)) (fun x => by
      by_cases hx : autoEnergyGradientSq eta₂ x=0
      · simp only [hx,zero_mul]
        exact mul_nonneg (sq_nonneg D) (mul_nonneg (sq_nonneg (eta₁ x)) (autoEnergyGradientSq_nonneg f x))
      · have heq := hcover x (auto_gradientSq_support_subset eta₂ hx)
        rw [heq,one_pow,one_mul]
        exact mul_le_mul_of_nonneg_right (hDb x) (autoEnergyGradientSq_nonneg f x))
    rw [integral_const_mul] at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hgrad (sq_nonneg D)]
  have hs₂sq : Function.support (fun x => (eta₂ x)^2)⊆S := by
    intro x hx
    apply hs₂
    apply subset_closure
    intro hz
    exact hx (by change (eta₂ x)^2=0; rw [hz]; norm_num)
  have hsource : (∫ x, (eta₂ x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2)≤I₂*W := by
    have hh := auto_weighted_square_bound (w := fun x => (eta₂ x)^2) (he₂.continuous.pow 2)
      (auto_cutoff_sq_compact hc₂) (fun x => sq_nonneg _) hs₂sq
      (auto_energy_trace_continuous hf _) hB hBt
    change (∫ x, (eta₂ x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix f x))^2)≤B^2*I₂ at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_right hBW hI₂]
  have hmatrix : ∀ x, |Matrix.trace ((A : Mat n)*secondFDerivMatrix eta₂ x)|≤K*‖secondFDerivMatrix eta₂ x‖ := by
    intro x
    have hh := abs_trace_mul_le (A : Mat n) (secondFDerivMatrix eta₂ x)
    have hAn : ‖(A : Mat n)‖≤(2*n : ℝ)*L := slopeSet_norm_le hell.le hA
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAn (Real.sqrt_nonneg _)) (norm_nonneg _))
  have hK : 0≤K := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (hell.le.trans hL))
  have htr : (∫ x, (f x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix eta₂ x))^2)≤K^2*J₂*W := by
    have hint₁ : Integrable (fun x => (f x)^2*(Matrix.trace ((A : Mat n)*secondFDerivMatrix eta₂ x))^2) :=
      ((hf.continuous.pow 2).mul ((auto_energy_trace_continuous he₂ _).pow 2)).integrable_of_hasCompactSupport
        (auto_cutoff_sq_compact (auto_energy_trace_compact he₂ hc₂ _)).mul_left
    have hint₂ : Integrable (fun x => ‖secondFDerivMatrix eta₂ x‖^2*(f x)^2) :=
      ((auto_hessian_sq_continuous he₂).mul (hf.continuous.pow 2)).integrable_of_hasCompactSupport
        (auto_hessian_sq_compact hc₂).mul_right
    have hh := integral_mono hint₁ (hint₂.const_mul (K^2)) (fun x => by
      have hb := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr (hmatrix x)
      rw [sq_abs,mul_pow] at hb
      nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg (f x))])
    rw [integral_const_mul] at hh
    have hw := auto_weighted_square_bound (auto_hessian_sq_continuous he₂) (auto_hessian_sq_compact hc₂)
      (fun x => sq_nonneg _) ((auto_hessian_sq_support_subset eta₂).trans hs₂) hf.continuous hM hMf
    change (∫ x, ‖secondFDerivMatrix eta₂ x‖^2*(f x)^2)≤M^2*J₂ at hw
    nlinarith only [hh,mul_le_mul_of_nonneg_left hw (sq_nonneg K),
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMW hJ₂) (sq_nonneg K)]
  have hen := auto_cutoff_hessian_energy hell hL hA hf he₂ hc₂
  have htotal : ell^2*(∫ x, ‖secondFDerivMatrix (fun y => eta₂ y*f y) x‖^2)≤E*W := by
    dsimp only [E]
    have hp := mul_le_mul_of_nonneg_left hcross (by positivity : 0≤12*L^2)
    nlinarith only [hen,hsource,hp,htr]
  have hdiv : (∫ x, ‖secondFDerivMatrix (fun y => eta₂ y*f y) x‖^2)≤(E/ell^2)*W := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (sq_pos_of_pos hell)).mpr (by simpa only [mul_comm (ell^2)] using htotal)
  nlinarith only [hdiv,hW]

/-- Actual localized elliptic L² energy: the constant precedes A, the trace budget, and f. -/
theorem auto_local_hessian_energy (n : ℕ) {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {r R : ℝ} (hr : 0<r) (hrR : r<R) :
    ∃ C : ℝ, 0<C ∧ ∀ A : Sym n, A∈slopeSet n ell L →
      ∀ M B : ℝ, 0≤M → 0≤B → ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      (∀ x∈Metric.ball (0 : Space n) R, |f x|≤M) →
      (∀ x∈Metric.ball (0 : Space n) R,
        |Matrix.trace ((A : Mat n)*secondFDerivMatrix f x)|≤B) →
      IntegrableOn (fun x => ‖secondFDerivMatrix f x‖^2) (Metric.ball (0 : Space n) r) ∧
      (∫ x in Metric.ball (0 : Space n) r, ‖secondFDerivMatrix f x‖^2)≤C*(M^2+B^2) := by
  let q := (r+R)/2
  let eta₁ : ContDiffBump (0 : Space n) :=
    ⟨q,(q+R)/2,by dsimp only [q]; linarith,by dsimp only [q]; linarith⟩
  let eta₂ : ContDiffBump (0 : Space n) := ⟨r,q,hr,by dsimp only [q]; linarith⟩
  have hs₁ : tsupport eta₁⊆Metric.ball (0 : Space n) R := by
    intro x hx
    rw [eta₁.tsupport_eq] at hx
    change dist x 0≤(q+R)/2 at hx
    change dist x 0<R
    dsimp only [q] at hx
    linarith
  have hs₂ : tsupport eta₂⊆Metric.ball (0 : Space n) R := by
    intro x hx
    rw [eta₂.tsupport_eq] at hx
    change dist x 0≤q at hx
    change dist x 0<R
    dsimp only [q] at hx
    linarith
  have hcover : ∀ x∈tsupport eta₂, eta₁ x=1 := by
    intro x hx
    apply eta₁.one_of_mem_closedBall
    rwa [eta₂.tsupport_eq] at hx
  obtain ⟨C,hC,hbound⟩ := auto_nested_cutoff_hessian_bound hell hL eta₁.contDiff eta₂.contDiff
    eta₁.hasCompactSupport eta₂.hasCompactSupport hs₁ hs₂ hcover
  refine ⟨C,hC,?_⟩
  intro A hA M B hM hB f hf hMf hBt
  have heq : EqOn (fun x => secondFDerivMatrix (fun y => eta₂ y*f y) x)
      (secondFDerivMatrix f) (Metric.ball (0 : Space n) r) := by
    intro x hx
    have hp : (fun y => eta₂ y*f y)=ᶠ[𝓝 x] f := by
      filter_upwards [eta₂.eventuallyEq_one_of_mem_ball hx] with y hy
      change eta₂ y=1 at hy
      simp only [hy,one_mul]
    have hd : fderiv ℝ (fun y => eta₂ y*f y)=ᶠ[𝓝 x] fderiv ℝ f := hp.fderiv
    have hdd := hd.fderiv_eq (𝕜 := ℝ)
    ext i j
    change (fderiv ℝ (fderiv ℝ (fun y => eta₂ y*f y)) x) (Yau.realVec i) (Yau.realVec j)=
      (fderiv ℝ (fderiv ℝ f) x) (Yau.realVec i) (Yau.realVec j)
    rw [hdd]
  have hi := auto_hessian_norm_sq_integrable (eta₂.contDiff.mul hf) eta₂.hasCompactSupport.mul_right
  have heqsq : EqOn (fun x => ‖secondFDerivMatrix (fun y => eta₂ y*f y) x‖^2)
      (fun x => ‖secondFDerivMatrix f x‖^2) (Metric.ball (0 : Space n) r) :=
    fun x hx => congrArg (fun H : Mat n => ‖H‖^2) (heq hx)
  refine ⟨hi.integrableOn.congr_fun heqsq measurableSet_ball,?_⟩
  rw [← setIntegral_congr_fun measurableSet_ball heqsq]
  exact (setIntegral_le_integral hi (ae_of_all volume fun x => sq_nonneg _)).trans
    (hbound A hA M B hM hB f hf hMf hBt)

end Yau.LeafProofs.L05AutonomousAux
