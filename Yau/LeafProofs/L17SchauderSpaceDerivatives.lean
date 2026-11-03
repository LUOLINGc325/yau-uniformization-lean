import Yau.LeafProofs.L17SchauderSpace

open Set Metric MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)

def functionHolderCLM : SchauderSpace P T gamma hT →L[ℝ] HolderSpace P T gamma :=
  (ambientFunctionHolderCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def gradientHolderCLM : SchauderSpace P T gamma hT →L[ℝ] LocalHolderSpace (D1 n) P T gamma :=
  (ambientGradientHolderCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def hessianHolderCLM : SchauderSpace P T gamma hT →L[ℝ] LocalHolderSpace (D2 n) P T gamma :=
  (rawTwoCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def timeHolderCLM : SchauderSpace P T gamma hT →L[ℝ] HolderSpace P T gamma :=
  (rawTimeCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL

def functionCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (Cylinder M T) ℝ :=
  (ambientValueCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def gradientCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (LocalCylinder P T) (D1 n) :=
  (ambientGradientCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def hessianCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (LocalCylinder P T) (D2 n) :=
  (ambientHessianCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL
def timeCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (Cylinder M T) ℝ :=
  (ambientTimeCLM P T gamma).comp (SchauderSpace P T gamma hT).subtypeL

variable {P T gamma hT}

def schauderFun (u : SchauderSpace P T gamma hT) : Cylinder M T → ℝ := functionCLM P T gamma hT u
def gradientFun (u : SchauderSpace P T gamma hT) : LocalCylinder P T → D1 n := gradientCLM P T gamma hT u
def hessianFun (u : SchauderSpace P T gamma hT) : LocalCylinder P T → D2 n := hessianCLM P T gamma hT u
def timeFun (u : SchauderSpace P T gamma hT) : Cylinder M T → ℝ := timeCLM P T gamma hT u

theorem schauderFun_continuous (u : SchauderSpace P T gamma hT) : Continuous (schauderFun u) :=
  (functionCLM P T gamma hT u).continuous
theorem gradientFun_continuous (u : SchauderSpace P T gamma hT) : Continuous (gradientFun u) :=
  (gradientCLM P T gamma hT u).continuous
theorem hessianFun_continuous (u : SchauderSpace P T gamma hT) : Continuous (hessianFun u) :=
  (hessianCLM P T gamma hT u).continuous
theorem timeFun_continuous (u : SchauderSpace P T gamma hT) : Continuous (timeFun u) :=
  (timeCLM P T gamma hT u).continuous

theorem spatialFTC (u : SchauderSpace P T gamma hT) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    schauderFun u (chartPoint P T p (z',t))-schauderFun u (chartPoint P T p (z,t)) =
      ∫ theta in (0 : ℝ)..1, gradientFun u (localSegmentPath P T p z z' t theta) ((z' : ComplexVector n)-z) := by
  have h := (u.property.1 p z z' t).1
  exact sub_eq_zero.mp h

theorem gradientFTC (u : SchauderSpace P T gamma hT) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    gradientFun u ⟨p,(z',t)⟩-gradientFun u ⟨p,(z,t)⟩ =
      ∫ theta in (0 : ℝ)..1, hessianFun u (localSegmentPath P T p z z' t theta) ((z' : ComplexVector n)-z) := by
  have h := (u.property.1 p z z' t).2
  exact sub_eq_zero.mp h

theorem timeFTC (u : SchauderSpace P T gamma hT) (x : M.Carrier) (s t : Time T) :
    schauderFun u (x,t)-schauderFun u (x,s) = ∫ tau in (s : ℝ)..(t : ℝ), timeFun u (closedTimePath T hT x tau) := by
  have h := u.property.2.1 x s t
  exact sub_eq_zero.mp h

theorem schauderFun_initial (u : SchauderSpace P T gamma hT) (x : M.Carrier) :
    schauderFun u (x,⟨0,⟨le_rfl,hT.le⟩⟩) = 0 := u.property.2.2 x

def chartFunction (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T)
    (z : ComplexVector n) : ℝ := schauderFun u (P.charts.chart p z,t)
def chartGradient (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T)
    (z : ComplexVector n) : D1 n := by
  classical
  exact if hz : z ∈ ball (0 : ComplexVector n) P.radius then gradientFun u ⟨p,(⟨z,hz⟩,t)⟩ else 0
def chartHessian (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T)
    (z : ComplexVector n) : D2 n := by
  classical
  exact if hz : z ∈ ball (0 : ComplexVector n) P.radius then hessianFun u ⟨p,(⟨z,hz⟩,t)⟩ else 0

theorem chartGradient_continuousOn (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T) :
    ContinuousOn (chartGradient u p t) (ball (0 : ComplexVector n) P.radius) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun z : ↥(ball (0 : ComplexVector n) P.radius) => gradientFun u ⟨p,(z,t)⟩) :=
    (gradientFun_continuous u).comp (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const))
  convert h using 1
  funext z
  simp only [Set.domRestrict_apply,chartGradient,dite_eq_left z.property]

theorem chartHessian_continuousOn (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T) :
    ContinuousOn (chartHessian u p t) (ball (0 : ComplexVector n) P.radius) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun z : ↥(ball (0 : ComplexVector n) P.radius) => hessianFun u ⟨p,(z,t)⟩) :=
    (hessianFun_continuous u).comp (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const))
  convert h using 1
  funext z
  simp only [Set.domRestrict_apply,chartHessian,dite_eq_left z.property]

theorem chartFunction_hasFDerivAt (u : SchauderSpace P T gamma hT) (p : P.centers)
    (t : Time T) {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius) :
    HasFDerivAt (chartFunction u p t) (gradientFun u ⟨p,(⟨z,hz⟩,t)⟩) z := by
  have h := hasFDerivAt_of_segment_integral isOpen_ball (convex_ball (0 : ComplexVector n) P.radius)
    (chartGradient_continuousOn u p t) (f := chartFunction u p t) ?_ hz
  · simpa only [chartGradient,dite_eq_left hz] using h
  · intro x hx y hy
    rw [show chartFunction u p t y-chartFunction u p t x =
      schauderFun u (chartPoint P T p (⟨y,hy⟩,t))-schauderFun u (chartPoint P T p (⟨x,hx⟩,t)) from rfl,
      spatialFTC u p ⟨x,hx⟩ ⟨y,hy⟩ t]
    apply intervalIntegral.integral_congr
    intro theta htheta
    have ht : theta ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htheta
    have hs := (convex_ball (0 : ComplexVector n) P.radius).lineMap_mem hx hy ht
    change gradientFun u ⟨p,(chartSegment P ⟨x,hx⟩ ⟨y,hy⟩ theta,t)⟩ (y-x) = _
    simp only [chartGradient,dite_eq_left hs]
    have hseg : chartSegment P ⟨x,hx⟩ ⟨y,hy⟩ theta = ⟨AffineMap.lineMap x y theta,hs⟩ :=
      Subtype.ext (chartSegment_of_mem P _ _ ht)
    rw [hseg]

theorem chartGradient_hasFDerivAt (u : SchauderSpace P T gamma hT) (p : P.centers)
    (t : Time T) {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius) :
    HasFDerivAt (chartGradient u p t) (hessianFun u ⟨p,(⟨z,hz⟩,t)⟩) z := by
  have h := hasFDerivAt_of_segment_integral isOpen_ball (convex_ball (0 : ComplexVector n) P.radius)
    (chartHessian_continuousOn u p t) (f := chartGradient u p t) ?_ hz
  · simpa only [chartHessian,dite_eq_left hz] using h
  · intro x hx y hy
    simp only [chartGradient,dite_eq_left hx,dite_eq_left hy]
    rw [gradientFTC u p ⟨x,hx⟩ ⟨y,hy⟩ t]
    apply intervalIntegral.integral_congr
    intro theta htheta
    have ht : theta ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htheta
    have hs := (convex_ball (0 : ComplexVector n) P.radius).lineMap_mem hx hy ht
    change hessianFun u ⟨p,(chartSegment P ⟨x,hx⟩ ⟨y,hy⟩ theta,t)⟩ (y-x) = _
    simp only [chartHessian,dite_eq_left hs]
    have hseg : chartSegment P ⟨x,hx⟩ ⟨y,hy⟩ theta = ⟨AffineMap.lineMap x y theta,hs⟩ :=
      Subtype.ext (chartSegment_of_mem P _ _ ht)
    rw [hseg]

/-- The second stored jet is the derivative of the actual first Frechet derivative. -/
theorem chartFunction_hasSecondFDerivAt (u : SchauderSpace P T gamma hT) (p : P.centers)
    (t : Time T) {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius) :
    HasFDerivAt (fderiv ℝ (chartFunction u p t)) (hessianFun u ⟨p,(⟨z,hz⟩,t)⟩) z := by
  apply (chartGradient_hasFDerivAt u p t hz).congr_of_eventuallyEq
  filter_upwards [show ∀ᶠ y in 𝓝 z, y ∈ ball (0 : ComplexVector n) P.radius from isOpen_ball.mem_nhds hz] with y hy
  simpa only [chartGradient,dite_eq_left hy] using (chartFunction_hasFDerivAt u p t hy).fderiv

theorem schauderFun_hasDerivWithinAt (u : SchauderSpace P T gamma hT)
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun tau => schauderFun u (closedTimePath T hT x tau)) (timeFun u (x,t))
      (Icc (0 : ℝ) T) (t : ℝ) := by
  have hw : Continuous (fun tau => timeFun u (closedTimePath T hT x tau)) :=
    (timeFun_continuous u).comp (closedTimePath_continuous T hT x)
  have h := hasDerivWithinAt_of_interval_integral hT.le hw
    (f := fun tau => schauderFun u (closedTimePath T hT x tau)) ?_ t.property
  · simpa only [closedTimePath,projIcc_val] using h
  · intro s hs r hr
    simpa only [closedTimePath,projIcc_of_mem hT.le hs,projIcc_of_mem hT.le hr] using timeFTC u x ⟨s,hs⟩ ⟨r,hr⟩

end Yau.LeafProofs.L17SchauderAux
