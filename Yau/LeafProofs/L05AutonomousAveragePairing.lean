import Yau.LeafProofs.L05AutonomousMollifierAverage
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The literal spatial probability average, with no derivative supplied by its definition. -/
def autoSpatialAverage {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∫ y, f (x+y) ∂μ

theorem auto_compact_tensor {n : ℕ} {φ f : Space n → ℝ}
    (hφ : HasCompactSupport φ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : Space n × Space n => φ p.1*f p.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hφ.prod hf)
  intro p hp
  exact ⟨subset_tsupport φ (left_ne_zero_of_mul hp),subset_tsupport f (right_ne_zero_of_mul hp)⟩

/-- Both integrands in the spatial change of variables have actual compact support in the product. -/
theorem auto_pairing_compact {n : ℕ} {φ f : Space n → ℝ}
    (hφ : HasCompactSupport φ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : Space n × Space n => φ p.1*f (p.1+p.2)) ∧
      HasCompactSupport (fun p : Space n × Space n => f p.1*φ (p.1-p.2)) := by
  constructor
  · have hh := (auto_compact_tensor hφ hf).comp_isClosedEmbedding
      (Homeomorph.shearAddRight (Space n)).isClosedEmbedding
    simpa only [Function.comp_def,Homeomorph.shearAddRight_coe] using hh
  · have hh := (auto_compact_tensor hf hφ).comp_isClosedEmbedding
      (Homeomorph.shearAddRight (Space n)).isClosedEmbedding
    have hn := hh.comp_isClosedEmbedding
      (Homeomorph.prodCongr (Homeomorph.refl (Space n)) (Homeomorph.neg (Space n))).isClosedEmbedding
    have hmap : (Homeomorph.prodCongr (Homeomorph.refl (Space n)) (Homeomorph.neg (Space n)) :
        Space n × Space n → Space n × Space n)=(fun p => (p.1,-p.2)) := rfl
    simpa only [Function.comp_def,Homeomorph.shearAddRight_coe,hmap,sub_eq_add_neg] using hn

/-- Fubini and the actual Haar translation give the adjoint of spatial averaging. -/
theorem auto_spatial_average_pairing {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {φ f : Space n → ℝ} (hφ : Continuous φ) (hf : Continuous f)
    (hcφ : HasCompactSupport φ) (hcf : HasCompactSupport f) :
    Integrable (fun x => φ x*autoSpatialAverage μ f x) ∧
      Integrable (fun x => f x*(∫ y, φ (x-y) ∂μ)) ∧
      (∫ x, φ x*autoSpatialAverage μ f x)=(∫ x, f x*(∫ y, φ (x-y) ∂μ)) := by
  have hcompact := auto_pairing_compact hcφ hcf
  have hcont₁ : Continuous (fun p : Space n × Space n => φ p.1*f (p.1+p.2)) :=
    (hφ.comp continuous_fst).mul (hf.comp (continuous_fst.add continuous_snd))
  have hcont₂ : Continuous (fun p : Space n × Space n => f p.1*φ (p.1-p.2)) :=
    (hf.comp continuous_fst).mul (hφ.comp (continuous_fst.sub continuous_snd))
  have hi₁ : Integrable (fun p : Space n × Space n => φ p.1*f (p.1+p.2)) (volume.prod μ) :=
    hcont₁.integrable_of_hasCompactSupport hcompact.1
  have hi₂ : Integrable (fun p : Space n × Space n => f p.1*φ (p.1-p.2)) (volume.prod μ) :=
    hcont₂.integrable_of_hasCompactSupport hcompact.2
  have heq₁ : (fun x => ∫ y, φ x*f (x+y) ∂μ)=(fun x => φ x*autoSpatialAverage μ f x) := by
    funext x
    exact integral_const_mul _ _
  have heq₂ : (fun x => ∫ y, f x*φ (x-y) ∂μ)=(fun x => f x*(∫ y, φ (x-y) ∂μ)) := by
    funext x
    exact integral_const_mul _ _
  refine ⟨by simpa only [← heq₁] using hi₁.integral_prod_left,
    by simpa only [← heq₂] using hi₂.integral_prod_left,?_⟩
  calc
    _ = ∫ y, (∫ x, φ x*f (x+y)) ∂μ := by
      rw [← heq₁]
      exact integral_integral_swap hi₁
    _ = ∫ y, (∫ x, f x*φ (x-y)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ fun y => by
        have htrans := integral_add_right_eq_self (μ := volume) (fun x => φ (x-y)*f x) y
        simpa only [add_sub_cancel_right,mul_comm] using htrans
    _ = _ := by
      rw [← heq₂]
      exact (integral_integral_swap hi₂).symm

/-- Symmetry moves the averaging operator to the fixed cutoff, including all integrability facts. -/
theorem auto_symmetric_average_commutator {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (hneg : ∀ g : Space n → ℝ, (∫ y, g (-y) ∂μ)=∫ y, g y ∂μ)
    {φ f : Space n → ℝ} (hφ : Continuous φ) (hf : Continuous f)
    (hcφ : HasCompactSupport φ) (hcf : HasCompactSupport f) :
    Integrable (fun x => φ x*(autoSpatialAverage μ f x-f x)) ∧
      Integrable (fun x => f x*(autoSpatialAverage μ φ x-φ x)) ∧
      (∫ x, φ x*(autoSpatialAverage μ f x-f x))=
        ∫ x, f x*(autoSpatialAverage μ φ x-φ x) := by
  have hsym (x : Space n) : (∫ y, φ (x-y) ∂μ)=autoSpatialAverage μ φ x := by
    have hh := hneg (fun y => φ (x-y))
    simpa only [sub_neg_eq_add,autoSpatialAverage] using hh.symm
  obtain ⟨hi₁,hi₂,heq⟩ := auto_spatial_average_pairing μ hφ hf hcφ hcf
  simp_rw [hsym] at hi₂ heq
  have hib : Integrable (fun x => φ x*f x) :=
    (hφ.mul hf).integrable_of_hasCompactSupport (hcφ.mul_right (f' := f))
  have hibr : Integrable (fun x => f x*φ x) := by simpa only [mul_comm] using hib
  have heq₁ : (fun x => φ x*(autoSpatialAverage μ f x-f x))=
      (fun x => φ x*autoSpatialAverage μ f x-φ x*f x) := by funext x;ring
  have heq₂ : (fun x => f x*(autoSpatialAverage μ φ x-φ x))=
      (fun x => f x*autoSpatialAverage μ φ x-f x*φ x) := by funext x;ring
  rw [heq₁,heq₂]
  exact ⟨hi₁.sub hib,hi₂.sub hibr,by rw [integral_sub hi₁ hib,integral_sub hi₂ hibr,heq];simp only [mul_comm]⟩

end Yau.LeafProofs.L05AutonomousAux
