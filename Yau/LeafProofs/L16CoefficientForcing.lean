import Yau.LeafProofs.L16InteriorCoefficients

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem finite_dot_square_le {ι : Type*} [Fintype ι] {a H : ι → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i, |a i| ≤ C) :
    (∑ i, a i*H i)^2 ≤ (Fintype.card ι : ℝ)*C^2*(∑ i, (H i)^2) := by
  have hA (i : ι) : (a i)^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hC).2 (ha i)
  calc
    _ ≤ (Fintype.card ι : ℝ)*(∑ i, (a i*H i)^2) := by
      simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => a i*H i)
    _ ≤ (Fintype.card ι : ℝ)*(∑ i, C^2*(H i)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hA i) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem finite_matrix_flux_square_le {n : ℕ} {A : Mat n} {H : Yau.RIdx n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i j, |A i j| ≤ C) :
    (∑ i : Yau.RIdx n, (∑ j : Yau.RIdx n, A i j*H j)^2) ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*C^2*(∑ j, (H j)^2) := by
  calc
    _ ≤ ∑ _i : Yau.RIdx n, (Fintype.card (Yau.RIdx n) : ℝ)*C^2*(∑ j, (H j)^2) :=
      Finset.sum_le_sum (fun i _ => finite_dot_square_le hC (hA i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem continuous_bounded_mul_memLp {n : ℕ} {μ : Measure (Point n)} {g u : Point n → ℝ} {C : ℝ}
    (hg : Continuous g) (hBound : ∀ p, |g p| ≤ C) (hu : MemLp u 2 μ) :
    MemLp (fun p => g p*u p) 2 μ := by
  have hTop : MemLp g (⊤ : ENNReal) μ := memLp_top_of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hBound p))
  exact hTop.mul hu

theorem bounded_matrix_flux_memLp {n : ℕ} {a : Point n → Mat n}
    {H : Point n → Yau.RIdx n → ℝ} {C : ℝ}
    (ha : Continuous a) (hBound : ∀ p, ‖a p‖ ≤ C)
    (hH : ∀ i, MemLp (fun p => H p i) 2 volume) (i : Yau.RIdx n) :
    MemLp (fun p => energyFlux a H p i) 2 volume := by
  apply memLp_finsetSum Finset.univ
  intro j _
  apply continuous_bounded_mul_memLp (C := C) ((matrixEntryCLM i j).continuous.comp ha) _ (hH j)
  intro p
  exact (frobenius_entry_abs_le (a p) i j).trans (hBound p)

theorem bounded_drift_dot_memLp {n : ℕ} {c H : Point n → Yau.RIdx n → ℝ} {C : ℝ}
    (hc : ∀ i, Continuous (fun p => c p i)) (hBound : ∀ p i, |c p i| ≤ C)
    (hH : ∀ i, MemLp (fun p => H p i) 2 volume) :
    MemLp (fun p => ∑ i, c p i*H p i) 2 volume := by
  exact memLp_finsetSum Finset.univ (fun i _ => continuous_bounded_mul_memLp (hc i)
    (fun p => hBound p i) (hH i))

theorem integrable_sum_component_sq {n : ℕ} {H : Point n → Yau.RIdx n → ℝ}
    (hH : ∀ i, MemLp (fun p => H p i) 2 volume) :
    Integrable (fun p => ∑ i, (H p i)^2) volume := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have h := (memLp_two_iff_integrable_sq_norm (hH i).aestronglyMeasurable).mp (hH i)
  simpa only [Real.norm_eq_abs,sq_abs] using h

theorem integral_flux_square_sum_le {n : ℕ} {a : Point n → Mat n}
    {H : Point n → Yau.RIdx n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (ha : Continuous a) (hBound : ∀ p, ‖a p‖ ≤ C)
    (hH : ∀ i, MemLp (fun p => H p i) 2 volume) :
    (∫ p, ∑ i, (energyFlux a H p i)^2) ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*C^2*(∫ p, ∑ i, (H p i)^2) := by
  have hF (i : Yau.RIdx n) := bounded_matrix_flux_memLp ha hBound hH i
  have hInt := integrable_sum_component_sq hH
  calc
    _ ≤ ∫ p, ((Fintype.card (Yau.RIdx n) : ℝ)^2*C^2)*(∑ i, (H p i)^2) := by
      apply integral_mono (integrable_sum_component_sq hF) (hInt.const_mul _)
      intro p
      exact finite_matrix_flux_square_le hC (fun i j => (frobenius_entry_abs_le (a p) i j).trans (hBound p))
    _ = _ := integral_const_mul _ _

theorem integral_drift_dot_square_le {n : ℕ} {c H : Point n → Yau.RIdx n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i, Continuous (fun p => c p i)) (hBound : ∀ p i, |c p i| ≤ C)
    (hH : ∀ i, MemLp (fun p => H p i) 2 volume) :
    (∫ p, (∑ i, c p i*H p i)^2) ≤
      (Fintype.card (Yau.RIdx n) : ℝ)*C^2*(∫ p, ∑ i, (H p i)^2) := by
  have hf := bounded_drift_dot_memLp hc hBound hH
  have hfInt : Integrable (fun p => (∑ i, c p i*H p i)^2) volume := by
    have h := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    simpa only [Real.norm_eq_abs,sq_abs] using h
  calc
    _ ≤ ∫ p, ((Fintype.card (Yau.RIdx n) : ℝ)*C^2)*(∑ i, (H p i)^2) := by
      apply integral_mono hfInt ((integrable_sum_component_sq hH).const_mul _)
      intro p
      exact finite_dot_square_le hC (hBound p)
    _ = _ := integral_const_mul _ _

theorem spatialDifferenceQuotient_forcing_L2_bounds {n : ℕ}
    {a : Point n → Mat n} {c H : Point n → Yau.RIdx n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ContDiff ℝ ∞ a) (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hH : ∀ j, MemLp (fun p => H p j) 2 volume) (e : Space n) (h : ℝ)
    (hADq : ∀ p, ‖spatialDifferenceQuotient a e h p‖ ≤ C)
    (hCDq : ∀ p j, |spatialDifferenceQuotient (fun q => c q j) e h p| ≤ C) :
    (∀ j, MemLp (fun p => energyFlux (spatialDifferenceQuotient a e h) H p j) 2 volume) ∧
      MemLp (fun p => ∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j) 2 volume ∧
      ((∫ p, ∑ j, (energyFlux (spatialDifferenceQuotient a e h) H p j)^2)+
        (∫ p, (∑ j, spatialDifferenceQuotient (fun q => c q j) e h p*H p j)^2)) ≤
        (((Fintype.card (Yau.RIdx n) : ℝ)^2+(Fintype.card (Yau.RIdx n) : ℝ))*C^2)*
          (∫ p, ∑ j, (H p j)^2) := by
  have hACont := (contDiff_spatialDifferenceQuotient ha e h).continuous
  have hCCont (j : Yau.RIdx n) := (contDiff_spatialDifferenceQuotient (hc j) e h).continuous
  refine ⟨fun j => bounded_matrix_flux_memLp hACont hADq hH j,
    bounded_drift_dot_memLp hCCont hCDq hH,?_⟩
  have hFlux := integral_flux_square_sum_le hC hACont hADq hH
  have hDrift := integral_drift_dot_square_le hC hCCont hCDq hH
  calc
    _ ≤ (Fintype.card (Yau.RIdx n) : ℝ)^2*C^2*(∫ p, ∑ j, (H p j)^2)+
        (Fintype.card (Yau.RIdx n) : ℝ)*C^2*(∫ p, ∑ j, (H p j)^2) := add_le_add hFlux hDrift
    _ = _ := by ring

end Yau.LeafProofs.L16Aux
