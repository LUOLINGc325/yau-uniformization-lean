import Yau.Proofs.P06ScalarSmoothHeatHilbert
import Yau.Proofs.P06WeitzenbockCoreMaps
import Yau.Proofs.G04SignedOrderBounds

/-! Every smooth bounded scalar is the actual trace of a smooth bounded
real (1,1) datum, with the original metric normalization. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 L18Aux G04Aux
variable {n : ℕ} {M : ComplexManifold n}

def scalarTraceDatum (g : HermitianField M) (f : M.Carrier → ℝ) : RealForm M 2 :=
  multiplyRealForm (fun x => f x / (n : ℝ)) (omegaForm g)

theorem scalarTraceDatum_oneOne (g : HermitianField M) (f : M.Carrier → ℝ) :
    RealOneOne (scalarTraceDatum g f) := by
  intro x u v
  change f x / (n : ℝ) * omegaForm g x ![Complex.I • u,Complex.I • v] =
    f x / (n : ℝ) * omegaForm g x ![u,v]
  rw [omegaForm_oneOne g x u v]

theorem scalarTraceDatum_trace (g : HermitianField M) (f : M.Carrier → ℝ)
    (hn : 0 < n) : formTrace g (scalarTraceDatum g f) = f := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext x
  rw [formTrace_eq_inner_omega g _ (scalarTraceDatum_oneOne g f) x]
  change formInner g (multiplyRealForm (fun x => f x / (n : ℝ)) (omegaForm g)) (omegaForm g) x = f x
  rw [multiplyRealForm_inner_left]
  change f x / (n : ℝ) * formNormSq g (omegaForm g) x = f x
  rw [P06Weitzenbock.omegaForm_normSq]
  exact div_mul_cancel₀ _ hnR

theorem scalarTraceDatum_bounded (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (hn : 0 < n) :
    BoundedOneOneData g.form (scalarTraceDatum g.form f) := by
  obtain ⟨C,hb⟩ := hb
  let D := max C 0
  let a := fun x => f x / (n : ℝ)
  have hD : 0 ≤ D := le_max_right _ _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : SmoothFn a := by
    simpa only [a,div_eq_mul_inv] using smoothFn_mul hf (smoothFn_const (n : ℝ)⁻¹)
  have hA : SmoothRealForm (scalarTraceDatum g.form f) :=
    smoothRealForm_multiply a (omegaForm g.form) ha
      (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g))
  have h11 := scalarTraceDatum_oneOne g.form f
  let B := ((n : ℝ)+1) * (D+1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨hA,h11,B,hB,order_of_norm g.form _ h11 hB ?_⟩
  intro x
  have hax : |a x| ≤ D := by
    dsimp only [a]
    rw [abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    exact ((hb x).trans (le_max_left C 0)).trans (by nlinarith)
  have hsq : (a x)^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a x)) hD).mpr hax
  have hnb : (n : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ)]
  have hdb : D^2 ≤ (D+1)^2 := by nlinarith
  change formNormSq g.form (multiplyRealForm a (omegaForm g.form)) x ≤ B^2
  rw [multiplyRealForm_normSq,P06Weitzenbock.omegaForm_normSq]
  calc
    _ ≤ D^2 * (n : ℝ) := mul_le_mul_of_nonneg_right hsq hnR.le
    _ = (n : ℝ) * D^2 := mul_comm _ _
    _ ≤ ((n : ℝ)+1)^2 * (D+1)^2 := mul_le_mul hnb hdb (sq_nonneg _) (sq_nonneg _)
    _ = B^2 := by dsimp only [B]; ring

end Yau.NodeProofs.P06Aux.ScalarSmooth
