import Yau.Proofs.C05ThirdScalarTimeDefinitions

/-! True matrix product derivatives on the original localized flow. -/
noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.Proofs.C05ThirdScalarTimeAux
open Yau Blueprint Yau.Proofs.C05Aux Set
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem ricci_endomorphism_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    let B := (gMat (h t) x)⁻¹ * ricci (h t) x
    let C := (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x
    HasDerivAt (fun s => ((gMat (h s) x)⁻¹ * ricci (h s) x) i j)
      ((B * B + C) i j) t := by
  simpa only [Matrix.mul_assoc] using hasDerivAt_complex_matrix_mul
    (gMat_inverse_hasDerivAt o h U P ρ hf x ht)
    (ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht) i j

theorem scalar_levi_endomorphism_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    let B := (gMat (h t) x)⁻¹ * ricci (h t) x
    let C := (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x
    let D := (gMat (h t) x)⁻¹ * levi (fun y => deriv (fun s => scalarCurvature (h s) y) t) x
    HasDerivAt (fun s => ((gMat (h s) x)⁻¹ * levi (scalarCurvature (h s)) x) i j)
      ((B * C + D) i j) t := by
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  simpa only [timeDeriv, Matrix.mul_assoc] using hasDerivAt_complex_matrix_mul
    (gMat_inverse_hasDerivAt o h U P ρ hf x ht)
    (hasDerivAt_levi_of_smoothSpaceTime isOpen_Ioi hu x ht) i j

theorem ricciLeviPairing_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ricciLeviPairing (h s) (scalarCurvature (h s)) x)
      (2 * ricciSquareLevi (h t) x + leviScalarSquare (h t) x +
        ricciLeviPairing (h t) (fun y => deriv (fun s => scalarCurvature (h s) y) t) x) t := by
  let B (s : ℝ) := (gMat (h s) x)⁻¹ * ricci (h s) x
  let C (s : ℝ) := (gMat (h s) x)⁻¹ * levi (scalarCurvature (h s)) x
  let D := (gMat (h t) x)⁻¹ * levi (fun y => deriv (fun s => scalarCurvature (h s) y) t) x
  have hB : ∀ i j, HasDerivAt (fun s => B s i j) ((B t * B t + C t) i j) t :=
    ricci_endomorphism_hasDerivAt o h U P ρ hf x ht
  have hC : ∀ i j, HasDerivAt (fun s => C s i j) ((B t * C t + D) i j) t :=
    scalar_levi_endomorphism_hasDerivAt o h U P ρ hf x ht
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_complex_trace_mul hB hC)
  change HasDerivAt (fun s => (B s * C s).trace.re)
    (((B t * B t + C t) * C t + B t * (B t * C t + D)).trace.re) t at hd
  have he : ((B t * B t + C t) * C t + B t * (B t * C t + D)).trace =
      2 * (B t * B t * C t).trace + (C t * C t).trace + (B t * D).trace := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.mul_assoc]
    ring
  rw [he] at hd
  convert hd using 1 <;>
    simp only [ricciLeviPairing, ricciSquareLevi, leviScalarSquare, traceWith,
      B, C, D, Matrix.mul_assoc, Complex.add_re, Complex.mul_re] <;> norm_num <;> ring

theorem ricciCube_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ricciCube (h s) x)
      (3 * ricciQuartic (h t) x + 3 * ricciSquareLevi (h t) x) t := by
  let B (s : ℝ) := (gMat (h s) x)⁻¹ * ricci (h s) x
  let C := (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x
  have hB : ∀ i j, HasDerivAt (fun s => B s i j) ((B t * B t + C) i j) t :=
    ricci_endomorphism_hasDerivAt o h U P ρ hf x ht
  have hBB := hasDerivAt_complex_matrix_mul hB hB
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_complex_trace_mul hBB hB)
  change HasDerivAt (fun s => (B s * B s * B s).trace.re)
    ((((B t * B t + C) * B t + B t * (B t * B t + C)) * B t +
      (B t * B t) * (B t * B t + C)).trace.re) t at hd
  have hcyc₁ : (C * (B t * B t)).trace = (B t * (B t * C)).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm C (B t * B t)
  have hcyc₂ : (B t * (C * B t)).trace = (B t * (B t * C)).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B t * C) (B t)
  have he : (((B t * B t + C) * B t + B t * (B t * B t + C)) * B t +
      (B t * B t) * (B t * B t + C)).trace =
        3 * (B t * B t * B t * B t).trace + 3 * (B t * B t * C).trace := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.mul_assoc]
    rw [hcyc₁, hcyc₂]
    ring
  rw [he] at hd
  convert hd using 1 <;>
    simp only [ricciCube, ricciQuartic, ricciSquareLevi, B, C, Matrix.mul_assoc,
      Complex.add_re, Complex.mul_re] <;> norm_num <;> ring

end Yau.Proofs.C05ThirdScalarTimeAux
