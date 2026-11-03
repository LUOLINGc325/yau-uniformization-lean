import Yau.Blueprint.ParabolicSpaces

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def qnorm2 {n : ℕ} (z : Point n) : ℝ := ‖z.1‖^2+z.2^2

theorem qnorm2_nonneg {n : ℕ} (z : Point n) : 0 ≤ qnorm2 z := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_sq_le_qnorm2 {n : ℕ} (z : Point n) : ‖z‖^2 ≤ qnorm2 z := by
  rw [Prod.norm_def]
  by_cases h : ‖z.1‖ ≤ ‖z.2‖
  · rw [max_eq_right h]
    simp only [Real.norm_eq_abs,sq_abs,qnorm2]
    nlinarith [sq_nonneg ‖z.1‖]
  · rw [max_eq_left (le_of_not_ge h)]
    unfold qnorm2
    nlinarith [sq_nonneg z.2]

theorem qnorm2_continuous {n : ℕ} : Continuous (qnorm2 (n := n)) := by
  unfold qnorm2
  fun_prop

/-- Global penalized maxima are genuine attained extrema. The localization
uses only a finite ball and the displayed lower quadratic bound. -/
theorem penalizedSup_attained {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {v P : E → ℝ} {B epsilon : ℝ} (hv : Continuous v) (hP : Continuous P)
    (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon)
    (z : E) (hPz : P z = 0) (hquad : ∀ q, ‖z-q‖^2 ≤ P q) :
    ∃ q, IsMaxOn (fun q => v q-P q/(2*epsilon)) Set.univ q ∧ P q ≤ 4*B*epsilon := by
  let radius := 2*B*epsilon+1
  have hr : 0 < radius := by dsimp [radius]; positivity
  let cost : E → ℝ := fun q => v q-P q/(2*epsilon)
  have hc : Continuous cost := hv.sub (hP.div_const _)
  have hz : z ∈ Metric.closedBall z radius := Metric.mem_closedBall_self hr.le
  obtain ⟨q,hq,hmax⟩ := (ProperSpace.isCompact_closedBall z radius).exists_isMaxOn ⟨z,hz⟩ hc.continuousOn
  have hglobal : IsMaxOn cost Set.univ q := by
    intro y _hy
    by_cases hy : y ∈ Metric.closedBall z radius
    · exact hmax hy
    have hnorm : radius ≤ ‖z-y‖ := by
      have hh : radius < dist y z := lt_of_not_ge hy
      simpa only [dist_eq_norm,norm_sub_rev] using hh.le
    have hnormsq := pow_le_pow_left₀ hr.le hnorm 2
    have hPbig : 4*B*epsilon ≤ P y := by
      have hh := hquad y
      dsimp only [radius] at hnormsq
      nlinarith [sq_nonneg (2*B*epsilon)]
    have hpenalty : 2*B ≤ P y/(2*epsilon) :=
      (le_div_iff₀ (by positivity : 0 < 2*epsilon)).2 (by nlinarith)
    have hybound := (abs_le.mp (hb y)).2
    have hzbound := (abs_le.mp (hb z)).1
    have hcost : cost y ≤ cost z := by
      dsimp [cost]
      rw [hPz,zero_div,sub_zero]
      linarith
    exact hcost.trans (hmax hz)
  refine ⟨q,hglobal,?_⟩
  have hmaxz := hglobal (Set.mem_univ z)
  have hqB := (abs_le.mp (hb q)).2
  have hzB := (abs_le.mp (hb z)).1
  change v z-P z/(2*epsilon) ≤ v q-P q/(2*epsilon) at hmaxz
  rw [hPz,zero_div,sub_zero] at hmaxz
  have hp : P q/(2*epsilon) ≤ 2*B := by linarith
  have hh := (div_le_iff₀ (by positivity : 0 < 2*epsilon)).1 hp
  nlinarith

def supRegularize {n : ℕ} (epsilon : ℝ) (v : Point n → ℝ) (z : Point n) : ℝ :=
  sSup {r | ∃ q : Point n, r = v q-qnorm2 (z-q)/(2*epsilon)}

theorem supRegularize_attained {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon)
    (z : Point n) : ∃ q,
      supRegularize epsilon v z = v q-qnorm2 (z-q)/(2*epsilon) ∧
      (∀ y, v y-qnorm2 (z-y)/(2*epsilon) ≤ v q-qnorm2 (z-q)/(2*epsilon)) ∧
      qnorm2 (z-q) ≤ 4*B*epsilon := by
  obtain ⟨q,hq,hdisp⟩ := penalizedSup_attained hv
    (qnorm2_continuous.comp (continuous_const.sub continuous_id)) hB hb hepsilon z
    (by simp [qnorm2]) (fun q => norm_sq_le_qnorm2 (z-q))
  have hupper : BddAbove {r | ∃ y : Point n, r = v y-qnorm2 (z-y)/(2*epsilon)} := by
    refine ⟨B,?_⟩
    rintro r ⟨y,rfl⟩
    exact sub_le_self _ (div_nonneg (qnorm2_nonneg _) (by positivity)) |>.trans (abs_le.mp (hb y)).2
  have hnon : ({r | ∃ y : Point n, r = v y-qnorm2 (z-y)/(2*epsilon)} : Set ℝ).Nonempty :=
    ⟨v q-qnorm2 (z-q)/(2*epsilon),q,rfl⟩
  refine ⟨q,?_,fun y => hq (Set.mem_univ y),hdisp⟩
  unfold supRegularize
  apply le_antisymm
  · apply csSup_le hnon
    rintro r ⟨y,rfl⟩
    exact hq (Set.mem_univ y)
  · exact le_csSup hupper ⟨q,rfl⟩

theorem le_supRegularize {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon)
    (z q : Point n) : v q-qnorm2 (z-q)/(2*epsilon) ≤ supRegularize epsilon v z := by
  obtain ⟨r,hr,hmax,_⟩ := supRegularize_attained hv hB hb hepsilon z
  rw [hr]
  exact hmax q

theorem supRegularize_bounds {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon)
    (z : Point n) : v z ≤ supRegularize epsilon v z ∧ |supRegularize epsilon v z| ≤ B := by
  obtain ⟨q,hq,_,_⟩ := supRegularize_attained hv hB hb hepsilon z
  have hlo : v z ≤ supRegularize epsilon v z := by
    simpa [qnorm2] using le_supRegularize hv hB hb hepsilon z z
  refine ⟨hlo,abs_le.mpr ⟨(abs_le.mp (hb z)).1.trans hlo,?_⟩⟩
  rw [hq]
  exact (sub_le_self _ (div_nonneg (qnorm2_nonneg _) (by positivity))).trans (abs_le.mp (hb q)).2

theorem qnorm2_sub {n : ℕ} (z q : Point n) :
    qnorm2 (z-q) = qnorm2 z+qnorm2 q-2*(inner ℝ z.1 q.1+z.2*q.2) := by
  simp only [qnorm2,Prod.fst_sub,Prod.snd_sub,norm_sub_sq_real]
  ring

theorem qnorm2_difference_affine {n : ℕ} (z w q : Point n) {a b : ℝ} (hab : a+b=1) :
    qnorm2 (a • z+b • w)-qnorm2 (a • z+b • w-q) =
      a*(qnorm2 z-qnorm2 (z-q))+b*(qnorm2 w-qnorm2 (w-q)) := by
  rw [qnorm2_sub,qnorm2_sub,qnorm2_sub]
  simp only [Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    inner_add_left,inner_smul_left,conj_trivial,smul_eq_mul]
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem supRegularize_semiconvex {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon) :
    ConvexOn ℝ Set.univ (fun z => supRegularize epsilon v z+qnorm2 z/(2*epsilon)) := by
  refine ⟨convex_univ,?_⟩
  intro z hz w hw a b ha hb' hab
  obtain ⟨q,hq,_,_⟩ := supRegularize_attained hv hB hb hepsilon (a • z+b • w)
  have hz' := mul_le_mul_of_nonneg_left (le_supRegularize hv hB hb hepsilon z q) ha
  have hw' := mul_le_mul_of_nonneg_left (le_supRegularize hv hB hb hepsilon w q) hb'
  have hquad := qnorm2_difference_affine z w q hab
  have hvsum : v q = a*v q+b*v q := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul]
  rw [hq]
  have hden : 2*epsilon ≠ 0 := by positivity
  have hid : v q-qnorm2 (a • z+b • w-q)/(2*epsilon)+qnorm2 (a • z+b • w)/(2*epsilon) =
      a*(v q-qnorm2 (z-q)/(2*epsilon))+b*(v q-qnorm2 (w-q)/(2*epsilon))+
        a*(qnorm2 z/(2*epsilon))+b*(qnorm2 w/(2*epsilon)) := by
    field_simp
    nlinarith [hquad,hvsum]
  rw [hid]
  nlinarith

def spatialInfRegularize {n : ℕ} (delta : ℝ) (u : Point n → ℝ) (z : Point n) : ℝ :=
  sInf {r | ∃ y : Space n, r = u (y,z.2)+‖z.1-y‖^2/(2*delta)}

theorem spatialInfRegularize_attained {n : ℕ} {u : Point n → ℝ} {B delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ q, |u q| ≤ B) (hdelta : 0 < delta)
    (z : Point n) : ∃ y,
      spatialInfRegularize delta u z = u (y,z.2)+‖z.1-y‖^2/(2*delta) ∧
      (∀ w, u (y,z.2)+‖z.1-y‖^2/(2*delta) ≤ u (w,z.2)+‖z.1-w‖^2/(2*delta)) ∧
      ‖z.1-y‖^2 ≤ 4*B*delta := by
  have hv : Continuous (fun y : Space n => -u (y,z.2)) :=
    (hu.comp (continuous_id.prodMk continuous_const)).neg
  have hP : Continuous (fun y : Space n => ‖z.1-y‖^2) := by fun_prop
  have hvB : ∀ y : Space n, |-u (y,z.2)| ≤ B := fun y => by simpa only [abs_neg] using hb (y,z.2)
  obtain ⟨y,hy,hdisp⟩ := penalizedSup_attained hv hP hB hvB hdelta z.1
    (by simp) (fun _ => le_rfl)
  have hmin (w : Space n) : u (y,z.2)+‖z.1-y‖^2/(2*delta) ≤
      u (w,z.2)+‖z.1-w‖^2/(2*delta) := by
    have hh : -u (w,z.2)-‖z.1-w‖^2/(2*delta) ≤ -u (y,z.2)-‖z.1-y‖^2/(2*delta) :=
      hy (Set.mem_univ w)
    linarith
  have hlower : BddBelow {r | ∃ w : Space n, r = u (w,z.2)+‖z.1-w‖^2/(2*delta)} := by
    refine ⟨-B,?_⟩
    rintro r ⟨w,rfl⟩
    exact (abs_le.mp (hb (w,z.2))).1.trans
      (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity)))
  have hnon : ({r | ∃ w : Space n, r = u (w,z.2)+‖z.1-w‖^2/(2*delta)} : Set ℝ).Nonempty :=
    ⟨u (y,z.2)+‖z.1-y‖^2/(2*delta),y,rfl⟩
  refine ⟨y,?_,hmin,hdisp⟩
  unfold spatialInfRegularize
  apply le_antisymm
  · exact csInf_le hlower ⟨y,rfl⟩
  · apply le_csInf hnon
    rintro r ⟨w,rfl⟩
    exact hmin w

theorem spatialInfRegularize_bounds {n : ℕ} {u : Point n → ℝ} {B delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ q, |u q| ≤ B) (hdelta : 0 < delta)
    (z : Point n) : spatialInfRegularize delta u z ≤ u z ∧ |spatialInfRegularize delta u z| ≤ B := by
  obtain ⟨y,hy,hmin,_⟩ := spatialInfRegularize_attained hu hB hb hdelta z
  have hupper : spatialInfRegularize delta u z ≤ u z := by
    have hh := hmin z.1
    simpa only [hy,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_div,add_zero,Prod.eta] using hh
  refine ⟨hupper,abs_le.mpr ⟨?_,hupper.trans (abs_le.mp (hb z)).2⟩⟩
  rw [hy]
  exact (abs_le.mp (hb (y,z.2))).1.trans
    (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity)))

theorem semiconvex_spatial_slice {n : ℕ} {u : Point n → ℝ} {epsilon : ℝ}
    (hu : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon))) (t : ℝ) :
    ConvexOn ℝ Set.univ (fun x : Space n => u (x,t)+‖x‖^2/(2*epsilon)) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hu.2 (Set.mem_univ (x,t)) (Set.mem_univ (y,t)) ha hb hab
  have he : a • (x,t)+b • (y,t) = (a • x+b • y,t) := by
    apply Prod.ext
    · rfl
    · simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul,← add_mul,hab,one_mul]
  rw [he] at hh
  simp only [qnorm2,add_div,smul_eq_mul] at hh ⊢
  have ht : a*(t^2/(2*epsilon))+b*(t^2/(2*epsilon)) = t^2/(2*epsilon) := by
    rw [← add_mul,hab,one_mul]
  nlinarith

theorem spatialInf_cost_strongConvex {n : ℕ} {u : Point n → ℝ} {epsilon delta : ℝ}
    (hu : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon))) (x : Space n) (t : ℝ) :
    StrongConvexOn Set.univ (delta⁻¹-epsilon⁻¹)
      (fun y : Space n => u (y,t)+‖x-y‖^2/(2*delta)) := by
  have hs := semiconvex_spatial_slice hu t
  have hl0 := (innerSL ℝ ((-delta⁻¹) • x)).toLinearMap.convexOn
    (convex_univ : Convex ℝ (Set.univ : Set (Space n)))
  have hl := hl0.add_const (‖x‖^2/(2*delta))
  apply strongConvexOn_iff_convex.mpr
  convert hs.add hl using 1
  funext y
  simp only [Pi.add_apply,ContinuousLinearMap.coe_coe,innerSL_apply_apply,real_inner_smul_left,
    norm_sub_sq_real]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem spatialInf_minimizer_unique {n : ℕ} {u : Point n → ℝ} {epsilon delta : ℝ}
    (hu : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon)))
    (hdelta : 0 < delta) (hde : delta < epsilon) (z : Point n) {y w : Space n}
    (hy : ∀ r : Space n, u (y,z.2)+‖z.1-y‖^2/(2*delta) ≤ u (r,z.2)+‖z.1-r‖^2/(2*delta))
    (hw : ∀ r : Space n, u (w,z.2)+‖z.1-w‖^2/(2*delta) ≤ u (r,z.2)+‖z.1-r‖^2/(2*delta)) : y=w := by
  have hm : 0 < delta⁻¹-epsilon⁻¹ := by
    exact sub_pos.mpr (by simpa only [one_div] using one_div_lt_one_div_of_lt hdelta hde)
  exact ((spatialInf_cost_strongConvex hu z.1 z.2).strictConvexOn hm).eq_of_isMinOn
    (fun r _ => hy r) (fun r _ => hw r) (Set.mem_univ y) (Set.mem_univ w)

theorem supRegularize_continuous {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon) :
    Continuous (supRegularize epsilon v) := by
  have hc := continuousOn_univ.mp ((supRegularize_semiconvex hv hB hb hepsilon).continuousOn isOpen_univ)
  apply (hc.sub (qnorm2_continuous.div_const (2*epsilon))).congr
  intro z
  change (supRegularize epsilon v z+qnorm2 z/(2*epsilon))-qnorm2 z/(2*epsilon) =
    supRegularize epsilon v z
  ring

theorem lasryLions_unique_spatial_minimum {n : ℕ} {v : Point n → ℝ} {B epsilon delta : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hde : delta < epsilon) (z : Point n) :
    ∃! y : Space n, ∀ w : Space n,
      supRegularize epsilon v (y,z.2)+‖z.1-y‖^2/(2*delta) ≤
        supRegularize epsilon v (w,z.2)+‖z.1-w‖^2/(2*delta) := by
  have hU := supRegularize_continuous hv hB hb hepsilon
  have hUb : ∀ q, |supRegularize epsilon v q| ≤ B :=
    fun q => (supRegularize_bounds hv hB hb hepsilon q).2
  obtain ⟨y,hy,hmin,hdisp⟩ := spatialInfRegularize_attained hU hB hUb hdelta z
  refine ⟨y,hmin,?_⟩
  intro w hw
  exact spatialInf_minimizer_unique (supRegularize_semiconvex hv hB hb hepsilon) hdelta hde z hw hmin

theorem spatialInfRegularize_le_candidate {n : ℕ} {u : Point n → ℝ} {B delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ q, |u q| ≤ B) (hdelta : 0 < delta)
    (z : Point n) (y : Space n) :
    spatialInfRegularize delta u z ≤ u (y,z.2)+‖z.1-y‖^2/(2*delta) := by
  obtain ⟨w,hw,hmin,_⟩ := spatialInfRegularize_attained hu hB hb hdelta z
  rw [hw]
  exact hmin y

theorem spatialInfRegularize_semiconcave {n : ℕ} {u : Point n → ℝ} {B delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ q, |u q| ≤ B) (hdelta : 0 < delta) (t : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : Space n => spatialInfRegularize delta u (x,t)-‖x‖^2/(2*delta)) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb' hab
  obtain ⟨w,hw,_,_⟩ := spatialInfRegularize_attained hu hB hb hdelta (a • x+b • y,t)
  have hx' := mul_le_mul_of_nonneg_left (spatialInfRegularize_le_candidate hu hB hb hdelta (x,t) w) ha
  have hy' := mul_le_mul_of_nonneg_left (spatialInfRegularize_le_candidate hu hB hb hdelta (y,t) w) hb'
  have hquad : ‖a • x+b • y‖^2-‖a • x+b • y-w‖^2 =
      a*(‖x‖^2-‖x-w‖^2)+b*(‖y‖^2-‖y-w‖^2) := by
    simpa only [qnorm2,Prod.fst_add,Prod.smul_fst,Prod.fst_sub,Prod.snd_add,Prod.smul_snd,
      Prod.snd_sub,smul_zero,add_zero,sub_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
      qnorm2_difference_affine ((x,0) : Point n) (y,0) (w,0) hab
  have huSum : u (w,t) = a*u (w,t)+b*u (w,t) := by rw [← add_mul,hab,one_mul]
  simp only [smul_eq_mul]
  rw [hw]
  have hid : u (w,t)+‖a • x+b • y-w‖^2/(2*delta)-‖a • x+b • y‖^2/(2*delta) =
      a*(u (w,t)+‖x-w‖^2/(2*delta)-‖x‖^2/(2*delta))+
        b*(u (w,t)+‖y-w‖^2/(2*delta)-‖y‖^2/(2*delta)) := by
    field_simp
    nlinarith [hquad,huSum]
  rw [hid]
  nlinarith

theorem supRegularize_error_lt {n : ℕ} {v : Point n → ℝ} {B epsilon rho eta : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon)
    (hrho : 0 < rho) (hscale : 4*B*epsilon < rho^2)
    (hmod : ∀ z q : Point n, dist z q < rho → |v z-v q| < eta) (z : Point n) :
    |supRegularize epsilon v z-v z| < eta := by
  obtain ⟨q,hq,_,hdisp⟩ := supRegularize_attained hv hB hb hepsilon z
  have hdist : dist q z < rho := by
    rw [dist_eq_norm,norm_sub_rev]
    have hh := (norm_sq_le_qnorm2 (z-q)).trans hdisp
    nlinarith [norm_nonneg (z-q)]
  have hdiff := hmod q z hdist
  have hlo := (supRegularize_bounds hv hB hb hepsilon z).1
  rw [abs_of_nonneg (sub_nonneg.mpr hlo),hq]
  have hpen : 0 ≤ qnorm2 (z-q)/(2*epsilon) := div_nonneg (qnorm2_nonneg _) (by positivity)
  linarith [le_abs_self (v q-v z)]

theorem lasryLions_uniformApprox {n : ℕ} {v : Point n → ℝ} {B : ℝ}
    (hv : UniformContinuous v) (hB : 0 < B) (hb : ∀ q, |v q| ≤ B) :
    ∀ eta : ℝ, 0 < eta → ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 → ∀ z : Point n,
        |spatialInfRegularize (epsilon/2) (supRegularize epsilon v) z-v z| < eta := by
  intro eta heta
  obtain ⟨rho,hrho,hmod⟩ := Metric.uniformContinuous_iff.mp hv eta heta
  refine ⟨rho^2/(4*B),by positivity,?_⟩
  intro epsilon hepsilon hsmall z
  have hscale : 4*B*epsilon < rho^2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*B)).1 hsmall
    nlinarith
  have hmod' : ∀ z q : Point n, dist z q < rho → |v z-v q| < eta :=
    fun z q hzq => by simpa only [Real.dist_eq] using hmod hzq
  have hU := supRegularize_continuous hv.continuous hB.le hb hepsilon
  have hUb : ∀ q, |supRegularize epsilon v q| ≤ B :=
    fun q => (supRegularize_bounds hv.continuous hB.le hb hepsilon q).2
  have hd : 0 < epsilon/2 := by positivity
  obtain ⟨y,hy,_,hdisp⟩ := spatialInfRegularize_attained hU hB.le hUb hd z
  have hdist : dist (y,z.2) z < rho := by
    rw [dist_eq_norm]
    have he : ‖(y,z.2)-z‖ = ‖z.1-y‖ := by
      simp only [Prod.sub_def,sub_self,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _),norm_sub_rev]
    rw [he]
    nlinarith [norm_nonneg (z.1-y)]
  have hlower := hmod' (y,z.2) z hdist
  have hupper := supRegularize_error_lt hv.continuous hB.le hb hepsilon hrho hscale hmod' z
  have hWu := (spatialInfRegularize_bounds hU hB.le hUb hd z).1
  have hUv := (supRegularize_bounds hv.continuous hB.le hb hepsilon (y,z.2)).1
  have hpen : 0 ≤ ‖z.1-y‖^2/(2*(epsilon/2)) := div_nonneg (sq_nonneg _) (by positivity)
  apply abs_lt.mpr
  constructor
  · rw [hy]
    linarith [(abs_lt.mp hlower).1]
  · linarith [(abs_lt.mp hupper).2]

end Yau.LeafProofs.L05Aux
