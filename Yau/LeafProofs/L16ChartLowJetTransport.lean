import Yau.LeafProofs.L16ChartCutoffBudget
import Yau.LeafProofs.L16ChartInverseDerivative

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartLowJetTransport_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartLowJetTransport_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartLowJetTransport_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartLowJetTransport_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Genuine Holder fields of linear maps compose with their actual operator norms. -/
theorem holderBound_clm_comp {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {α C D : ℝ} {Q : Set (Point n)}
    {A : Point n → F →L[ℝ] G} {B : Point n → E →L[ℝ] F}
    (hA : HolderBound α Q A C) (hB : HolderBound α Q B D) :
    HolderBound α Q (fun p => (A p).comp (B p)) (2*C*D) := by
  have hC : 0 ≤ C := hA.1
  have hD : 0 ≤ D := hB.1
  have hCD : 0 ≤ C*D := mul_nonneg hA.1 hB.1
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hA.2.1 p hp) (hB.2.1 p hp) (norm_nonneg _) hA.1)).trans (by nlinarith)
  · intro p hp q hq
    have hEq : (A p).comp (B p)-(A q).comp (B q) =
        (A p-A q).comp (B p)+(A q).comp (B p-B q) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply,sub_apply,add_apply,map_sub]
      abel
    rw [hEq]
    have hW : 0 ≤ holderWeight α p q := by dsimp only [holderWeight]; positivity
    have h1 := mul_le_mul (hA.2.2 p hp q hq) (hB.2.1 p hp) (norm_nonneg _) (mul_nonneg hA.1 hW)
    have h2 := mul_le_mul (hA.2.1 q hq) (hB.2.2 p hp q hq) (norm_nonneg _) hA.1
    calc
      _ ≤ ‖(A p-A q).comp (B p)‖+‖(A q).comp (B p-B q)‖ := norm_add_le _ _
      _ ≤ ‖A p-A q‖*‖B p‖+‖A q‖*‖B p-B q‖ := add_le_add
        (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ (C*holderWeight α p q)*D+C*(D*holderWeight α p q) := add_le_add h1 h2
      _ = _ := by ring

/-- A time-independent bounded Lipschitz field has a full parabolic Holder
    bound on its actual spatial set. -/
theorem holderBound_spatial_lipschitz_field {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {α T C : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C) {K : Set (Space n)} {f : Space n → E}
    (hBound : ∀ x ∈ K, ‖f x‖ ≤ C)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖f x-f y‖ ≤ C*‖x-y‖) :
    HolderBound α (cylinder K 0 T) (fun p => f p.1) (2*C) := by
  have hh := holderBound_of_small_parabolic_lipschitz (f := fun p : Point n => f p.1)
    (a := 0) (b := T) (O := K) (ρ := 1) (L := C) hα hα1
    (by norm_num) (by norm_num) hC
    (fun p hp => by simpa only [mul_one] using hBound p.1 hp.1)
    (fun x y t hx hy ht => hLip x hx y hy)
    (fun x t s hx ht hs => by simp only [sub_self,norm_zero]; positivity)
  simpa only [Real.one_rpow,mul_one] using hh

/-- Inside the true plateau, a spatial cutoff changes neither the value nor
    the actual ambient spatial derivative of an arbitrary function. -/
theorem cutoff_plateau_value_spatialD {n : ℕ} {φ : Space n → ℝ} (u : Point n → ℝ)
    {x : Space n} (hφ : ∀ᶠ y in 𝓝 x, φ y = 1) (t : ℝ) :
    φ x*u (x,t) = u (x,t) ∧
      spatialD (fun p => φ p.1*u p) (x,t) = spatialD u (x,t) := by
  have hx : x ∈ {y : Space n | φ y = 1} := mem_of_mem_nhds hφ
  refine ⟨by rw [hx,one_mul],?_⟩
  have hSlice : (fun y => φ y*u (y,t)) =ᶠ[𝓝 x] (fun y => u (y,t)) := by
    filter_upwards [hφ] with y hy
    rw [hy,one_mul]
  exact hSlice.fderiv_eq

/-- A cutoff equals one in a neighbourhood of every point of its strict
    inner plateau, including points on the model lateral face. -/
theorem innerPatchBump_eventually_one_of_norm_lt {n : ℕ} {r : ℝ} (hr : 0 < r) {c x : Space n}
    (hx : ‖x-c‖ < r) : ∀ᶠ y in 𝓝 x, innerPatchBump r hr c y = 1 := by
  have hxB : x ∈ Metric.ball c r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  filter_upwards [Metric.isOpen_ball.mem_nhds hxB] with y hy
  exact innerPatchBump_eq_one hr (by simpa only [Metric.mem_ball,dist_eq_norm] using (show dist y c < r from hy).le)

/-- The true inverse-Jacobian field is Holder on any compact convex buffer
    inside the actual chart target, with a constant fixed before boundary data. -/
theorem compact_chart_inverse_jacobian_holder {n : ℕ} {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {K : Set (Space n)} (hK : IsCompact K) (hConv : Convex ℝ K) (hKT : K ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧ HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ c (c.symm p.1)) C := by
  obtain ⟨C,hC,hNorm,hLip⟩ := compact_chart_inverse_jacobian_bound c hc hci hK hConv hKT
  exact ⟨2*C,by positivity,holderBound_spatial_lipschitz_field hα hα1 hC.le hNorm hLip⟩

/-- Recovering the original gradient preserves the actual local Holder
    control. Its only Holder inputs are the already proved cutoff low jets
    and the geometric inverse-Jacobian field. -/
theorem chart_lowPair_original_gradient_holder {n : ℕ} {α T C D : ℝ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {e : Space n} {K X : Set (Space n)} (hKT : K ⊆ c.target)
    (hKH : K ⊆ {x | 0 ≤ inner ℝ e x}) (hMap : MapsTo c.symm K X)
    {φ : Space n → ℝ} (hPlateau : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, φ y = 1)
    {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u)
    (hCut : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
      (fun p => (φ p.1*u (c.symm p.1,p.2),spatialD (fun q => φ q.1*u (c.symm q.1,q.2)) p)) C)
    (hJac : HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ c (c.symm p.1)) D) :
    HolderBound α (cylinder K 0 T) (fun p => (u (c.symm p.1,p.2),spatialD u (c.symm p.1,p.2))) (C+2*C*D) := by
  have hSub : cylinder K 0 T ⊆ cylinder {x | 0 ≤ inner ℝ e x} 0 T := fun p hp => ⟨hKH hp.1,hp.2⟩
  have hCutSmall := holderBound_mono hCut hSub
  have hVal : HolderBound α (cylinder K 0 T) (fun p => u (c.symm p.1,p.2)) C :=
    holderBound_congr_on (holderBound_fst hCutSmall) (fun p hp =>
      (cutoff_plateau_value_spatialD (chartSpaceTimePullback c.symm u) (hPlateau p.1 hp.1) p.2).1)
  have hGrad : HolderBound α (cylinder K 0 T)
      (fun p => spatialD (chartSpaceTimePullback c.symm u) p) C :=
    holderBound_congr_on (holderBound_snd hCutSmall) (fun p hp =>
      (cutoff_plateau_value_spatialD (chartSpaceTimePullback c.symm u) (hPlateau p.1 hp.1) p.2).2)
  have hProduct := holderBound_clm_comp hGrad hJac
  have hOrig : HolderBound α (cylinder K 0 T) (fun p => spatialD u (c.symm p.1,p.2)) (2*C*D) :=
    holderBound_congr_on hProduct (fun p hp => (spatialD_chart_recover c hc hci (hKT hp.1) p.2
      ((hu.2.2.2.2.1 (c.symm p.1,p.2) ⟨hMap hp.1,hp.2⟩).differentiableAt (by norm_num))).symm)
  have hVal' := holderBound_mono_const hVal (by linarith [hOrig.1] : C ≤ C+2*C*D)
  have hOrig' := holderBound_mono_const hOrig (by linarith [hVal.1] : 2*C*D ≤ C+2*C*D)
  refine ⟨hVal'.1,fun p hp => max_le (hVal'.2.1 p hp) (hOrig'.2.1 p hp),?_⟩
  intro p hp q hq
  exact max_le (hVal'.2.2 p hp q hq) (hOrig'.2.2 p hp q hq)

end Yau.LeafProofs.L16Aux
