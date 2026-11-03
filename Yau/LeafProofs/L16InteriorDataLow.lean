import Yau.LeafProofs.L16ChartLowJetTransport

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance interiorDataLow_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDataLow_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDataLow_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance interiorDataLow_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Restricting only the spatial set preserves actual parabolic C² structure;
    the nonempty time fibers remain precisely the same closed interval. -/
theorem c2_cylinder_mono_space {n : ℕ} {S X : Set (Space n)} {l r : ℝ}
    (hSX : S ⊆ X) {u : Point n → ℝ} (hu : C2 (cylinder X l r) u) :
    C2 (cylinder S l r) u := by
  have hSub : cylinder S l r ⊆ cylinder X l r := fun p hp => ⟨hSX hp.1,hp.2⟩
  refine ⟨hu.1.mono hSub,hu.2.1.mono hSub,hu.2.2.1.mono hSub,?_,
    fun p hp => hu.2.2.2.2.1 p (hSub hp),?_⟩
  · exact (hu.2.2.2.1.mono hSub).congr (fun p hp => timeD_cylinder_change_space u hp.1 (hSX hp.1))
  · intro p hp
    have hh := hu.2.2.2.2.2 p (hSub hp)
    have hpS := hp.1
    have hpX := hSX hp.1
    simpa only [Parabolic.cylinder,mem_prod,hpS,hpX,true_and] using hh

/-- Near every interior point, the original Schauder data supply an actual
    lower-jet Holder bound with neighbourhood and constant fixed beforehand. -/
theorem open_interior_data_low_holder {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {x : Space n} (hx : x ∈ O) {α T : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ Metric.closedBall x (4*δ) ⊆ O ∧
      ∀ (u : Point n → ℝ) P, SchauderBound α (cylinder (closure O) 0 T) u P →
        HolderBound α (cylinder (Metric.closedBall x δ) 0 T) (fun p => (u p,spatialD u p)) (A*P) := by
  obtain ⟨ε,hε,hεSub⟩ := Metric.isOpen_iff.mp hO x hx
  let δ := ε/8
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hBuffer : Metric.closedBall x (4*δ) ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp only [δ]; linarith : 4*δ < ε)).trans hεSub
  let V := Metric.ball x (4*δ)
  have hVO : V ⊆ O := Metric.ball_subset_closedBall.trans hBuffer
  let φ : Space n → ℝ := innerPatchBump (2*δ) (by positivity) x
  have hφ : ContDiff ℝ ∞ φ := innerPatchBump_contDiff (by positivity) x
  have hcφ : HasCompactSupport φ := (innerPatchBump (2*δ) (by positivity) x).hasCompactSupport
  have hSupport : tsupport φ ⊆ V := by
    rw [(innerPatchBump (2*δ) (by positivity) x).tsupport_eq]
    change Metric.closedBall x (3*(2*δ)/2) ⊆ Metric.ball x (4*δ)
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨E,hE,hφBound⟩ := compact_cutoff_actual_jet_bound hφ hcφ
  refine ⟨δ,64*E,hδ,by positivity,hBuffer,?_⟩
  intro u P hu
  have hP : 0 ≤ P := hu.2.1
  have huV : C2 (cylinder V 0 T) u := c2_cylinder_mono_space (fun y hy => subset_closure (hVO hy)) hu.1
  have huLocal : C2 (cylinder (univ∩V) 0 T) u := by simpa only [univ_inter] using huV
  have hRaw : ∀ p ∈ cylinder (univ∩V) 0 T,
      |u p| ≤ P ∧ ‖spatialD u p‖ ≤ P ∧ ‖spatialDD u p‖ ≤ P ∧
      |timeD (cylinder (univ∩V) 0 T) u p| ≤ P := by
    intro p hp
    have hpQ : p ∈ cylinder (closure O) 0 T := ⟨subset_closure (hVO hp.1.2),hp.2⟩
    have hTime : ‖timeD (cylinder (closure O) 0 T) u p‖ ≤ P := hu.2.2.2.2.2.1 p hpQ
    refine ⟨(hu.2.2.1 p hpQ).1,(hu.2.2.1 p hpQ).2,hu.2.2.2.1.2.1 p hpQ,?_⟩
    rw [timeD_cylinder_change_space u hp.1 hpQ.1]
    exact hTime
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hw : C2 (cylinder univ 0 T) (fun p => φ p.1*u p) :=
    c2_spatial_cutoff_relative_extension (show IsOpen V from Metric.isOpen_ball) hφ2 hSupport huLocal
  have hRawW := fun (p : Point n) (hp : p ∈ cylinder univ 0 T) =>
    cutoff_relative_raw_jet_bound hE.le hP hφ2 hSupport hφBound huLocal hRaw (p := p) hp
  have hLow := c2_global_lowPair_holder hα hα1 hT (by positivity : 0 ≤ 4*E*P) hw
    (fun p hp => ⟨(hRawW p hp).1,(hRawW p hp).2.2.1,(hRawW p hp).2.2.2⟩)
  have hSmall := holderBound_mono hLow (show cylinder (Metric.closedBall x δ) 0 T ⊆ cylinder univ 0 T from
    fun p hp => ⟨mem_univ _,hp.2⟩)
  have hBudget : 16*(4*E*P) = (64*E)*P := by ring
  rw [hBudget] at hSmall
  apply holderBound_congr_on hSmall
  intro p hp
  have hPlateau : ∀ᶠ y in 𝓝 p.1, φ y = 1 := by
    apply innerPatchBump_eventually_one_of_norm_lt (by positivity)
    have hh : ‖p.1-x‖ ≤ δ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hp.1
    linarith
  exact Prod.ext (cutoff_plateau_value_spatialD u hPlateau p.2).1 (cutoff_plateau_value_spatialD u hPlateau p.2).2

end Yau.LeafProofs.L16Aux
