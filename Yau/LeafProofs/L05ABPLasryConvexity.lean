import Yau.LeafProofs.L05ABPRegularization

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def lasryTimeLinear (n : ℕ) : (Point n × Space n) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp (ContinuousLinearMap.fst ℝ (Point n) (Space n))

def lasryJointLift (n : ℕ) : (Point n × Space n) →L[ℝ] Point n :=
  (ContinuousLinearMap.snd ℝ (Point n) (Space n)).prod (lasryTimeLinear n)

def lasrySpatialLinear (n : ℕ) (epsilon delta : ℝ) : (Point n × Space n) →L[ℝ] Space n :=
  (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp (ContinuousLinearMap.fst ℝ (Point n) (Space n))-
    ((epsilon-delta)/epsilon) • ContinuousLinearMap.snd ℝ (Point n) (Space n)

theorem lasry_quadratic_completion {n : ℕ} {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hde : delta < epsilon)
    (x y : Space n) (t : ℝ) :
    ‖x-y‖^2/(2*delta)+(‖x‖^2+t^2)/(2*(epsilon-delta))-(‖y‖^2+t^2)/(2*epsilon) =
      epsilon/(2*delta*(epsilon-delta))*‖x-((epsilon-delta)/epsilon) • y‖^2+
        delta/(2*epsilon*(epsilon-delta))*t^2 := by
  rw [norm_sub_sq_real,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right]
  field_simp [hepsilon.ne',hdelta.ne',sub_ne_zero.mpr hde.ne']
  ring

def lasryCorrectedCost {n : ℕ} (epsilon delta : ℝ) (u : Point n → ℝ)
    (r : Point n × Space n) : ℝ :=
  u (r.2,r.1.2)+‖r.1.1-r.2‖^2/(2*delta)+qnorm2 r.1/(2*(epsilon-delta))

theorem lasryCorrectedCost_convex {n : ℕ} {u : Point n → ℝ} {epsilon delta : ℝ}
    (hu : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon)))
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hde : delta < epsilon) :
    ConvexOn ℝ Set.univ (lasryCorrectedCost epsilon delta u) := by
  have hU : ConvexOn ℝ Set.univ
      (fun r : Point n × Space n => u (r.2,r.1.2)+qnorm2 (r.2,r.1.2)/(2*epsilon)) := by
    convert! hu.comp_linearMap (lasryJointLift n).toLinearMap using 1
  have hsp0 : ConvexOn ℝ Set.univ (fun r : Point n × Space n => ‖lasrySpatialLinear n epsilon delta r‖^2) := by
    convert!
      ((convexOn_univ_norm (E := Space n)).pow (fun _ _ => norm_nonneg _) 2).comp_linearMap
        (lasrySpatialLinear n epsilon delta).toLinearMap using 1
  have ht0 : ConvexOn ℝ Set.univ (fun r : Point n × Space n => (lasryTimeLinear n r)^2) := by
    convert!
      ((convexOn_univ_norm (E := ℝ)).pow (fun _ _ => norm_nonneg _) 2).comp_linearMap
        (lasryTimeLinear n).toLinearMap using 1
    funext r
    simp only [Function.comp_apply,Pi.pow_apply,Real.norm_eq_abs,sq_abs]
    rfl
  have hsp : 0 ≤ epsilon/(2*delta*(epsilon-delta)) := by positivity
  have ht : 0 ≤ delta/(2*epsilon*(epsilon-delta)) := by positivity
  have hc := hU.add ((hsp0.smul hsp).add (ht0.smul ht))
  convert hc using 1
  funext r
  change u (r.2,r.1.2)+‖r.1.1-r.2‖^2/(2*delta)+qnorm2 r.1/(2*(epsilon-delta)) =
    u (r.2,r.1.2)+qnorm2 (r.2,r.1.2)/(2*epsilon)+
      (epsilon/(2*delta*(epsilon-delta))*‖r.1.1-((epsilon-delta)/epsilon) • r.2‖^2+
        delta/(2*epsilon*(epsilon-delta))*r.1.2^2)
  have hh := lasry_quadratic_completion hepsilon hdelta hde r.1.1 r.2 r.1.2
  dsimp only [qnorm2]
  linarith

theorem spatialInfRegularize_joint_semiconvex {n : ℕ} {u : Point n → ℝ} {B epsilon delta : ℝ}
    (hu : Continuous u) (hB : 0 ≤ B) (hb : ∀ q, |u q| ≤ B)
    (hc : ConvexOn ℝ Set.univ (fun z => u z+qnorm2 z/(2*epsilon)))
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hde : delta < epsilon) :
    ConvexOn ℝ Set.univ (fun z => spatialInfRegularize delta u z+qnorm2 z/(2*(epsilon-delta))) := by
  refine ⟨convex_univ,?_⟩
  intro z hz w hw a b ha hb' hab
  obtain ⟨y,hy,_,_⟩ := spatialInfRegularize_attained hu hB hb hdelta z
  obtain ⟨v,hv,_,_⟩ := spatialInfRegularize_attained hu hB hb hdelta w
  have hmix := spatialInfRegularize_le_candidate hu hB hb hdelta (a • z+b • w) (a • y+b • v)
  have hcost := (lasryCorrectedCost_convex hc hepsilon hdelta hde).2
    (Set.mem_univ (z,y)) (Set.mem_univ (w,v)) ha hb' hab
  change lasryCorrectedCost epsilon delta u (a • (z,y)+b • (w,v)) ≤
    a*lasryCorrectedCost epsilon delta u (z,y)+b*lasryCorrectedCost epsilon delta u (w,v) at hcost
  have he : a • (z,y)+b • (w,v) = (a • z+b • w,a • y+b • v) := by rfl
  rw [he] at hcost
  simp only [lasryCorrectedCost] at hcost
  simp only [smul_eq_mul]
  rw [hy,hv]
  linarith

def jointSemiconvex {n : ℕ} (K : ℝ) (u : Point n → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun z => u z+(K/2)*qnorm2 z)

def spatialSemiconcave {n : ℕ} (K : ℝ) (u : Point n → ℝ) : Prop :=
  ∀ t : ℝ, ConcaveOn ℝ Set.univ (fun x : Space n => u (x,t)-(K/2)*‖x‖^2)

theorem lasryLions_semiconvex_semiconcave {n : ℕ} {v : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ q, |v q| ≤ B) (hepsilon : 0 < epsilon) :
    jointSemiconvex (2/epsilon) (spatialInfRegularize (epsilon/2) (supRegularize epsilon v)) ∧
      spatialSemiconcave (2/epsilon) (spatialInfRegularize (epsilon/2) (supRegularize epsilon v)) ∧
      ∀ z, |spatialInfRegularize (epsilon/2) (supRegularize epsilon v) z| ≤ B := by
  have hU := supRegularize_continuous hv hB hb hepsilon
  have hUb : ∀ q, |supRegularize epsilon v q| ≤ B :=
    fun q => (supRegularize_bounds hv hB hb hepsilon q).2
  have hd : 0 < epsilon/2 := by positivity
  have hde : epsilon/2 < epsilon := by linarith
  have hW := spatialInfRegularize_joint_semiconvex hU hB hUb
    (supRegularize_semiconvex hv hB hb hepsilon) hepsilon hd hde
  refine ⟨?_,?_,fun z => (spatialInfRegularize_bounds hU hB hUb hd z).2⟩
  · unfold jointSemiconvex
    convert! hW using 1
    funext z
    have hh : 2*(epsilon-epsilon/2) = epsilon := by ring
    rw [hh]
    ring
  · intro t
    have hs := spatialInfRegularize_semiconcave hU hB hUb hd t
    convert! hs using 1
    funext x
    have hh : 2*(epsilon/2) = epsilon := by ring
    rw [hh]
    ring

theorem locallyLipschitz_sub_real {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun z => f z-g z) := by
  intro z
  obtain ⟨K,s,hs,hfs⟩ := hf z
  obtain ⟨L,t,ht,hgt⟩ := hg z
  refine ⟨K+L,s ∩ t,Filter.inter_mem hs ht,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hfx := hfs.dist_le_mul x hx.1 y hy.1
  have hgx := hgt.dist_le_mul x hx.2 y hy.2
  change |(f x-g x)-(f y-g y)| ≤ ((K+L : NNReal) : ℝ)*dist x y
  have he : (f x-g x)-(f y-g y) = (f x-f y)-(g x-g y) := by ring
  rw [he,NNReal.coe_add]
  simp only [Real.dist_eq] at hfx hgx
  have hh := abs_sub (f x-f y) (g x-g y)
  nlinarith

theorem jointSemiconvex_locallyLipschitz {n : ℕ} {K : ℝ} {w : Point n → ℝ}
    (hw : jointSemiconvex K w) : LocallyLipschitz w := by
  have hq : ContDiff ℝ 1 (fun z : Point n => (K/2)*qnorm2 z) := by
    have hnorm : ContDiff ℝ 1 (fun z : Point n => ‖z.1‖^2) := contDiff_fst.norm_sq ℝ
    exact contDiff_const.mul (hnorm.add (contDiff_snd.pow 2))
  have hh := locallyLipschitz_sub_real hw.locallyLipschitz hq.locallyLipschitz
  simpa only [add_sub_cancel_right] using hh

/-- Only a compact buffered neighborhood is needed for the mollifier bounds;
this obtains its finite Lipschitz constant from genuine convex continuity. -/
theorem jointSemiconvex_lipschitzOn_compact {n : ℕ} {K : ℝ} {w : Point n → ℝ}
    (hw : jointSemiconvex K w) {D : Set (Point n)} (hD : IsCompact D) :
    ∃ C : NNReal, LipschitzOnWith C w D :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hD
    (jointSemiconvex_locallyLipschitz hw).locallyLipschitzOn

end Yau.LeafProofs.L05Aux
