import Yau.LeafProofs.L16TracePoissonInitial
import Yau.LeafProofs.L16NormalPoissonDifference

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePoissonAverage_sub_source_identity {n : ℕ} {a F : ℝ}
    (ha : 0 < a) {B : Point n → ℝ} (hB : Continuous B)
    (hF : ∀ p, |B p| ≤ F) (p : Point n) :
    tracePoissonAverage a B p-B p =
      ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
        (heatAverage r (fun y => B (y,p.2-r)) p.1-B p) := by
  have hProb := normalPoissonKernel_probability ha
  have hIp := tracePoissonAverage_integrable ha hB hF p
  have hIc := hProb.1.mul_const (B p)
  rw [tracePoissonAverage,ite_eq_right ha.ne']
  calc
    _ = (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
        heatAverage r (fun y => B (y,p.2-r)) p.1)-
        ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*B p := by
      rw [integral_mul_const,hProb.2,one_mul]
    _ = _ := by
      rw [← integral_sub hIp hIc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by ring

theorem tracePoissonAverage_difference_weighted_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F → ∀ a b : ℝ, 0 < a → 0 < b → ∀ p : Point n,
      |tracePoissonAverage b B p-tracePoissonAverage a B p| ≤ C*F*
        (∫ r in Set.Ioi (0 : ℝ), |normalPoissonKernel b r-normalPoissonKernel a r| *r^(α/2)) := by
  obtain ⟨C,hC,hHeat⟩ := retardedHeatAverage_sub_source_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro B F hB a b ha hb p
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSup : ∀ q, |B q| ≤ F := fun q => hB.2.1 q (Set.mem_univ _)
  let A : ℝ → ℝ := fun r => heatAverage r (fun y => B (y,p.2-r)) p.1-B p
  have hIa : IntegrableOn (fun r => normalPoissonKernel a r*A r) (Set.Ioi 0) := by
    have h := (tracePoissonAverage_integrable ha hCont hSup p).sub
      ((normalPoissonKernel_probability ha).1.mul_const (B p))
    exact h.congr (Filter.Eventually.of_forall fun r => by simp only [Pi.sub_apply]; dsimp only [A]; ring)
  have hIb : IntegrableOn (fun r => normalPoissonKernel b r*A r) (Set.Ioi 0) := by
    have h := (tracePoissonAverage_integrable hb hCont hSup p).sub
      ((normalPoissonKernel_probability hb).1.mul_const (B p))
    exact h.congr (Filter.Eventually.of_forall fun r => by simp only [Pi.sub_apply]; dsimp only [A]; ring)
  have hEq : tracePoissonAverage b B p-tracePoissonAverage a B p =
      ∫ r in Set.Ioi (0 : ℝ), (normalPoissonKernel b r-normalPoissonKernel a r)*A r := by
    calc
      _ = (tracePoissonAverage b B p-B p)-(tracePoissonAverage a B p-B p) := by ring
      _ = (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel b r*A r)-
          ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*A r := by
        rw [tracePoissonAverage_sub_source_identity hb hCont hSup,
          tracePoissonAverage_sub_source_identity ha hCont hSup]
      _ = _ := by
        rw [← integral_sub hIb hIa]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun r => by ring
  have hMoment := normalPoissonKernel_sub_weight_integrable
    (by linarith : α/2 < 1/2) ha hb
  rw [hEq,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), (C*F)*
        (|normalPoissonKernel b r-normalPoissonKernel a r| *r^(α/2)) := by
      apply norm_integral_le_of_norm_le (hMoment.const_mul (C*F))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_eq_abs,abs_mul]
      have h := mul_le_mul_of_nonneg_left (hHeat B F hB r hr p)
        (abs_nonneg (normalPoissonKernel b r-normalPoissonKernel a r))
      convert h using 1 <;> ring
    _ = _ := integral_const_mul _ _

theorem tracePoissonAverage_near_normal_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2*a → ∀ p : Point n,
      |tracePoissonAverage b B p-tracePoissonAverage a B p| ≤ C*F*(b-a)*a^(α-1) := by
  obtain ⟨CH,hCH,hHeat⟩ := tracePoissonAverage_difference_weighted_bound (n := n) hα hα1
  obtain ⟨CD,hCD,hDiff⟩ := normalPoissonKernel_sub_weighted_near hα hα1
  refine ⟨CH*CD,by positivity,?_⟩
  intro B F hB a b ha hab hba p
  have h := mul_le_mul_of_nonneg_left (hDiff a b ha hab hba).2
    (mul_nonneg hCH.le hB.1)
  exact (hHeat B F hB a b ha (ha.trans_le hab) p).trans (by convert h using 1 <;> ring)


theorem small_increment_rpow_interpolation {α a δ : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ ≤ a) :
    δ*a^(α-1) ≤ δ^α := by
  by_cases hδ0 : δ = 0
  · simp only [hδ0,zero_mul,Real.zero_rpow hα.ne',le_refl]
  have hδPos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  calc
    δ*a^(α-1) ≤ δ*δ^(α-1) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδPos hδa (by linarith)) hδ
    _ = δ^α := by
      simpa only [Real.rpow_one,show 1+(α-1) = α by ring] using
        (Real.rpow_add hδPos 1 (α-1)).symm

theorem tracePoissonAverage_normal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ p : Point n,
      |tracePoissonAverage a B p-tracePoissonAverage b B p| ≤ C*F*|a-b|^α := by
  obtain ⟨CT,hCT,hTrace⟩ := tracePoissonAverage_sub_source_bound (n := n) hα hα1
  obtain ⟨CN,hCN,hNear⟩ := tracePoissonAverage_near_normal_bound (n := n) hα hα1
  let C : ℝ := 1+CN+3*CT
  have hC : 0 < C := by dsimp only [C]; linarith
  have hCTC : CT ≤ C := by dsimp only [C]; linarith
  have hCNC : CN ≤ C := by dsimp only [C]; linarith
  have h3CTC : 3*CT ≤ C := by dsimp only [C]; linarith
  have hOrdered : ∀ (B : Point n → ℝ) (F : ℝ), HolderBound α Set.univ B F →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ p : Point n,
      |tracePoissonAverage b B p-tracePoissonAverage a B p| ≤ C*F*(b-a)^α := by
    intro B F hB a b ha hab p
    have hF : 0 ≤ F := hB.1
    have hb : 0 ≤ b := ha.trans hab
    have hδ : 0 ≤ b-a := sub_nonneg.mpr hab
    by_cases ha0 : a = 0
    · subst a
      rw [show tracePoissonAverage 0 B p = B p from ite_eq_left rfl]
      have h := (hTrace B F hB b hb p).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCTC hF)
          (Real.rpow_nonneg hb α))
      simpa only [sub_zero] using h
    have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hba : b ≤ 2*a
    · have hInterp := small_increment_rpow_interpolation hα hα1 haPos hδ
        (show b-a ≤ a by linarith)
      calc
        _ ≤ CN*F*(b-a)*a^(α-1) := hNear B F hB a b haPos hab hba p
        _ ≤ CN*F*(b-a)^α := by
          have h := mul_le_mul_of_nonneg_left hInterp (mul_nonneg hCN.le hF)
          convert h using 1 <;> ring
        _ ≤ C*F*(b-a)^α := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCNC hF) (Real.rpow_nonneg hδ α)
    · have haδ : a ≤ b-a := by linarith
      have hbδ : b ≤ 2*(b-a) := by linarith
      have hAPow := Real.rpow_le_rpow ha haδ hα.le
      have hBPow := Real.rpow_le_rpow hb hbδ hα.le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ] at hBPow
      have hTwo : (2 : ℝ)^α ≤ 2 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hα1.le
      have hBPow' : b^α ≤ 2*(b-a)^α := hBPow.trans
        (mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hδ α))
      have hTA := hTrace B F hB a ha p
      have hTB := hTrace B F hB b hb p
      have hABound := mul_le_mul_of_nonneg_left hAPow (mul_nonneg hCT.le hF)
      have hBBound := mul_le_mul_of_nonneg_left hBPow' (mul_nonneg hCT.le hF)
      calc
        _ ≤ |tracePoissonAverage b B p-B p|+|B p-tracePoissonAverage a B p| := abs_sub_le _ _ _
        _ ≤ (3*CT)*F*(b-a)^α := by
          rw [abs_sub_comm (B p)]
          linarith
        _ ≤ C*F*(b-a)^α := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h3CTC hF) (Real.rpow_nonneg hδ α)
  refine ⟨C,hC,?_⟩
  intro B F hB a b ha hb p
  rcases le_total a b with hab|hba
  · have hAbs : |a-b| = b-a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    rw [hAbs,abs_sub_comm (tracePoissonAverage a B p)]
    exact hOrdered B F hB a b ha hab p
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hOrdered B F hB b a hb hba p


/-- The real parabolic Poisson field is Holder jointly in its nonnegative
    normal height, tangent location and time. -/
theorem tracePoissonAverage_halfSpace_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : Space n, ‖e‖ = 1 →
      ∀ (B : Point n → ℝ) (F : ℝ), HolderBound α Set.univ B F →
      HolderBound α {p : Point n | 0 ≤ inner ℝ e p.1}
        (fun p => tracePoissonAverage (inner ℝ e p.1) B
          (halfSpaceBoundaryProjection e p.1,p.2)) (C*F) := by
  obtain ⟨CN,hCN,hNormal⟩ := tracePoissonAverage_normal_holder_bound (n := n) hα hα1
  refine ⟨CN+1,by linarith,?_⟩
  intro e he B F hB
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSup : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (Set.mem_univ _)
  refine ⟨mul_nonneg (by linarith) hB.1,?_,?_⟩
  · intro p hp
    change |tracePoissonAverage (inner ℝ e p.1) B
      (halfSpaceBoundaryProjection e p.1,p.2)| ≤ (CN+1)*F
    exact (tracePoissonAverage_bound hp hCont hSup _).trans (by
      have h := mul_nonneg hCN.le hB.1
      nlinarith)
  · intro p hp q hq
    change |tracePoissonAverage (inner ℝ e p.1) B
        (halfSpaceBoundaryProjection e p.1,p.2)-
      tracePoissonAverage (inner ℝ e q.1) B
        (halfSpaceBoundaryProjection e q.1,q.2)| ≤ (CN+1)*F*holderWeight α p q
    have hHeight := hNormal B F hB (inner ℝ e p.1) (inner ℝ e q.1) hp hq
      (halfSpaceBoundaryProjection e p.1,p.2)
    have hGap : |inner ℝ e p.1-inner ℝ e q.1| ≤ ‖p.1-q.1‖ := by
      have h := abs_real_inner_le_norm e (p.1-q.1)
      simpa only [inner_sub_right,he,one_mul] using h
    have hWeight : holderWeight α
        (halfSpaceBoundaryProjection e p.1,p.2)
        (halfSpaceBoundaryProjection e q.1,q.2) ≤ holderWeight α p q := by
      change ‖halfSpaceBoundaryProjection e p.1-halfSpaceBoundaryProjection e q.1‖^α+
          |p.2-q.2|^(α/2) ≤ ‖p.1-q.1‖^α+|p.2-q.2|^(α/2)
      exact add_le_add (Real.rpow_le_rpow (norm_nonneg _)
        (halfSpaceBoundaryProjection_nonexpansive e _ _) hα.le) le_rfl
    have hSpatial : ‖p.1-q.1‖^α ≤ holderWeight α p q := by
      dsimp only [holderWeight]
      linarith [Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)]
    have hHeightBound := hHeight.trans (mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow (abs_nonneg _) hGap hα.le).trans hSpatial)
      (mul_nonneg hCN.le hB.1))
    have hFixed := (tracePoissonAverage_fixed_normal_holder hα hq hB).2.2
      (halfSpaceBoundaryProjection e p.1,p.2) (Set.mem_univ _)
      (halfSpaceBoundaryProjection e q.1,q.2) (Set.mem_univ _)
    have hFixedBound := hFixed.trans (mul_le_mul_of_nonneg_left hWeight hB.1)
    calc
      _ ≤ |tracePoissonAverage (inner ℝ e p.1) B (halfSpaceBoundaryProjection e p.1,p.2)-
            tracePoissonAverage (inner ℝ e q.1) B (halfSpaceBoundaryProjection e p.1,p.2)|+
          |tracePoissonAverage (inner ℝ e q.1) B (halfSpaceBoundaryProjection e p.1,p.2)-
            tracePoissonAverage (inner ℝ e q.1) B (halfSpaceBoundaryProjection e q.1,q.2)| :=
        abs_sub_le _ _ _
      _ ≤ CN*F*holderWeight α p q+F*holderWeight α p q := add_le_add hHeightBound hFixedBound
      _ = _ := by ring

def boundaryTraceNormalJet {n : ℕ} (e : Space n) (T : ℝ) (B : Point n → ℝ) : Point n → ℝ :=
  fun p => -tracePoissonAverage (inner ℝ e p.1) (tracePastExtension T B)
    (halfSpaceBoundaryProjection e p.1,p.2)

theorem boundaryTraceNormalJet_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : Space n, ‖e‖ = 1 → ∀ T F : ℝ, 0 ≤ T →
      ∀ B : Point n → ℝ, HolderBound α (cylinder Set.univ 0 T) B F →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
        (boundaryTraceNormalJet e T B) (C*F) := by
  obtain ⟨C,hC,h⟩ := tracePoissonAverage_halfSpace_holder (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro e he T F hT B hB
  exact holderBound_mono (holderBound_neg (h e he _ F
    (tracePastExtension_holder hα.le hT hB))) (fun p hp => hp.1)

theorem boundaryTraceNormalJet_boundary {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (T : ℝ) (B : Point n → ℝ) {x : Space n} (hx : inner ℝ e x = 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : boundaryTraceNormalJet e T B (x,t) = -B (x,t) := by
  rw [boundaryTraceNormalJet,hx,tracePoissonAverage,ite_eq_left rfl,
    halfSpaceBoundaryProjection_apply he,hx]
  simp only [zero_smul,sub_zero]
  rw [tracePastExtension_eqOn T B ⟨Set.mem_univ _,ht⟩]

theorem boundaryTraceNormalJet_small_time_bound {n : ℕ} {e : Space n} {α T F : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F) (hB0 : ∀ x, B (x,0) = 0)
    {p : Point n} (hp : p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) :
    |boundaryTraceNormalJet e T B p| ≤ F*p.2^(α/2) := by
  rw [boundaryTraceNormalJet,abs_neg]
  exact tracePoissonAverage_small_time_bound hα hT hp.1 hB hB0 hp.2

end Yau.LeafProofs.L16Aux
