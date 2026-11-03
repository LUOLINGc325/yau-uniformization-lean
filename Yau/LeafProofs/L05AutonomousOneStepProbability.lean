import Yau.LeafProofs.L05AutonomousHarnackMean
import Yau.LeafProofs.L05AutonomousFiniteContractionExtrema

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual normalized product volume on the genuine earlier Harnack slab. -/
def oneStepEarlyProbability {n : ℕ} (c : Space n) (R T : ℝ) : Measure (Point n) :=
  ((volume : Measure (Point n)) (autoEarly c R T))⁻¹ •
    (volume : Measure (Point n)).restrict (autoEarly c R T)

theorem oneStepEarlyProbability_isProbability {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R) (T : ℝ) :
    IsProbabilityMeasure (oneStepEarlyProbability c R T) := by
  constructor
  simp only [oneStepEarlyProbability,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · intro hz
    have hp := autoEarly_mu_pos c hR T
    simp only [harnackMu,hz,ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  · exact autoEarly_measure_ne_top c R T

theorem oneStepEarlyProbability_integral {n : ℕ} (c : Space n) (R T : ℝ) (f : Point n → ℝ) :
    (∫ p, f p ∂oneStepEarlyProbability c R T)=
      (∫ p in autoEarly c R T, f p)/harnackMu (autoEarly c R T) := by
  rw [oneStepEarlyProbability,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul,harnackMu,div_eq_inv_mul]

theorem oneStepEarlyProbability_early_ae {n : ℕ} (c : Space n) (R T : ℝ) :
    ∀ᵐ p ∂oneStepEarlyProbability c R T, p∈autoEarly c R T :=
  Measure.ae_smul_measure (ae_restrict_mem (autoEarly_isOpen c R T).measurableSet) _

theorem oneStepEarlyProbability_lpMean {n : ℕ} (c : Space n) (R T p : ℝ) (f : Point n → ℝ) :
    (∫ q, (f q)^p ∂oneStepEarlyProbability c R T)^(1/p)=autoLpMean (autoEarly c R T) p f := by
  rw [oneStepEarlyProbability_integral]
  rfl

/-- Full measure of the actual goodset, on the genuine source region, supplies
the support assumption of the finite-family probability calculation. -/
theorem oneStepEarlyProbability_good_ae {n : ℕ} (c : Space n) (R T : ℝ)
    {O S : Set (Point n)} (hO : MeasurableSet O) (hEO : autoEarly c R T⊆O)
    (hFull : ∀ᵐ p ∂((volume : Measure (Point n)).restrict O), p∈S) :
    ∀ᵐ p ∂oneStepEarlyProbability c R T, p∈S∩autoEarly c R T := by
  have hGlobal := (ae_restrict_iff' hO).mp hFull
  have hEarly : ∀ᵐ p ∂((volume : Measure (Point n)).restrict (autoEarly c R T)), p∈S := by
    apply (ae_restrict_iff' (autoEarly_isOpen c R T).measurableSet).mpr
    filter_upwards [hGlobal] with p hp hpe
    exact hp (hEO hpe)
  have hGood : ∀ᵐ p ∂oneStepEarlyProbability c R T, p∈S := Measure.ae_smul_measure hEarly _
  filter_upwards [hGood,oneStepEarlyProbability_early_ae c R T] with p hp hpe
  exact ⟨hp,hpe⟩

/-- A literal pointwise Harnack mean bound passes to the genuine supremum,
without assuming its attainment or continuity. -/
theorem oneStep_mean_le_sup_deficit {X : Type*} {Q : Set X} (hQ : Q.Nonempty)
    (w : X → ℝ) {A CH M : ℝ} (hCH : 0 < CH)
    (hPoint : ∀ p∈Q, A ≤ CH*(M-w p)) :
    A ≤ CH*(M-finiteFieldSup w Q) := by
  have hValues : ∀ b∈w '' Q, b ≤ M-A/CH := by
    rintro b ⟨p,hp,rfl⟩
    have hd : A/CH ≤ M-w p := (div_le_iff₀ hCH).mpr (by simpa only [mul_comm] using hPoint p hp)
    linarith only [hd]
  have hSup : finiteFieldSup w Q ≤ M-A/CH := csSup_le (hQ.image w) hValues
  have hd : A/CH ≤ M-finiteFieldSup w Q := by linarith only [hSup]
  have hh := mul_le_mul_of_nonneg_left hd hCH.le
  have hc : CH*(A/CH)=A := by field_simp
  rwa [hc] at hh

end Yau.LeafProofs.L05AutonomousAux
