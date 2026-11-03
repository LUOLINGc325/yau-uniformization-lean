import Yau.Proofs.Y01PrimaryPolynomial
import Yau.Proofs.Y01EndpointGrowth
import Yau.Proofs.Y01RegularJump
import Yau.Proofs.Y01SequenceEnvelopes

/-! Both aligned jump polynomials have sqrt-clock coefficient bounds,
derived from the same original changes at the two endpoints. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof Yau.Proofs.Y02Aux
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem matOpNorm_nonneg_own (A : Herm n) : 0 ≤ matOpNorm A := norm_nonneg _

theorem alignedJump_two_endpoint_bound
    {E : Frames n} {L : Changes n} {reg : ℕ → Prop} {k : ℕ} {x y : ℝ}
    (hk : reg k) (hfinish : Unitary (E.finish k)) (hplus : IsUnit (L.plus k))
    (hplusBound : matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹ ≤ x)
    (hnextBound : matOpNorm (primaryDerivative reg E L (k + 1)) +
      matOpNorm (primaryDerivative reg E L (k + 1))⁻¹ ≤ y) :
    let J := if reg (k + 1) then alignedJump E L k else 1
    matOpNorm J + matOpNorm J⁻¹ ≤ 2 * x * y := by
  let Tnext := primaryDerivative reg E L (k + 1)
  let B := L.plus k * (E.finish k).conjTranspose
  let J := if reg (k + 1) then alignedJump E L k else 1
  have hBunit : IsUnit B := hplus.mul (unitary_isUnit (unitary_conjTranspose hfinish))
  have hBInv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBunit)
  have hfactor : Tnext = J * B := primary_next_factor hk hfinish hplus
  have hJform : J = Tnext * B⁻¹ := by
    rw [hfactor, Matrix.mul_assoc, hBInv, Matrix.mul_one]
  have hJinv : J⁻¹ = B * Tnext⁻¹ := by
    rw [hJform, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 hBunit)]
  have hBn : matOpNorm B = matOpNorm (L.plus k) :=
    matOpNorm_mul_unitary (unitary_conjTranspose hfinish) _
  have hBi : matOpNorm B⁻¹ = matOpNorm (L.plus k)⁻¹ := by
    dsimp only [B]
    rw [Matrix.mul_inv_rev, unitary_conjTranspose_inverse hfinish, matOpNorm_unitary_mul hfinish]
  have hB : matOpNorm B ≤ x := by
    rw [hBn]
    linarith [matOpNorm_nonneg_own (L.plus k)⁻¹]
  have hBiBound : matOpNorm B⁻¹ ≤ x := by
    rw [hBi]
    linarith [matOpNorm_nonneg_own (L.plus k)]
  have hT : matOpNorm Tnext ≤ y := by linarith [matOpNorm_nonneg_own Tnext⁻¹]
  have hTi : matOpNorm Tnext⁻¹ ≤ y := by linarith [matOpNorm_nonneg_own Tnext]
  have hx : 0 ≤ x := (matOpNorm_nonneg_own B).trans hB
  have hy : 0 ≤ y := (matOpNorm_nonneg_own Tnext).trans hT
  have hJnorm : matOpNorm J ≤ y * x := by
    rw [hJform]
    exact (norm_mul_le Tnext B⁻¹).trans
      (mul_le_mul hT hBiBound (matOpNorm_nonneg_own B⁻¹) hy)
  have hJinorm : matOpNorm J⁻¹ ≤ x * y := by
    rw [hJinv]
    exact (norm_mul_le B Tnext⁻¹).trans
      (mul_le_mul hB hTi (matOpNorm_nonneg_own Tnext⁻¹) hx)
  nlinarith

set_option diagnostics true in
theorem alignedJump_coeffNorm_sqrt_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps : ℝ}
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀)
    (hs2 : ∀ k, 2 ≤ gridClock Q N M hm j₀ k) {L : Changes n} {C c : ℝ} (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
        (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ k, reg k →
      (linearPoly (J k)).coeffNorm + (linearPoly (J k)⁻¹).coeffNorm ≤
        Real.exp (Cj * Real.sqrt (gridClock Q N M hm j₀ k)) := by
  let s := gridClock Q N M hm j₀
  let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let T := primaryDerivative reg E L
  obtain ⟨pt, hpt, hT⟩ := primaryDerivative_polynomial_bounds (F := F) (tk := tk) (E := E) (Q := Q) (N := N) (j₀ := j₀) (M := M) (hm := hm) (scale := scale) (K := K) (eps := eps) (L := L) (C := C) (c := c) hE hhm hgrid hc hL
  obtain ⟨pl, hpl, hP⟩ := aligned_plus_polynomial_bound (D := diagonal F tk E) (w := weight Q N M hm scale K eps j₀ (rate F tk E)) (S := macroClock hm) (Q := Q) (N := N) (j₀ := j₀) (M := M) (hm := hm) (L := L) (C := C) (c := c) hhm hgrid hL
  let p := max pt pl
  have hp : 0 ≤ p := hpl.trans (le_max_right _ _)
  have hs k : 1 ≤ s k := (by norm_num : (1 : ℝ) ≤ 2).trans (hs2 k)
  have hT' k : matOpNorm (T k) + matOpNorm (T k)⁻¹ ≤ (1 + s k) ^ p :=
    (hT k).trans (Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) (le_max_left _ _))
  have hP' k (hk : reg k) : matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹ ≤ (1 + s k) ^ p :=
    (hP k hk).trans (Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) (le_max_right _ _))
  obtain ⟨q, hpq, hq⟩ := endpoint_real_power_product hm p hp
  have hq0 : 0 ≤ q := hp.trans hpq
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  let K0 := 2 * (n : ℝ) ^ 2
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  refine ⟨K0 + 4 * |q|, by positivity, ?_⟩
  intro k hk
  have hJ := alignedJump_two_endpoint_bound (E := E) (L := L) (reg := reg) (k := k) (x := (1 + s k) ^ p) (y := (1 + s (k + 1)) ^ p) hk (hE k).2.2.2.1
    (plus_change_isUnit (hL k hk)) (hP' k hk) (hT' (k + 1))
  have hstep : s (k + 1) ≤ Real.exp hm * s k := by
    have h := (hsteps k).2.1
    change s (k + 1) - s k ≤ (Real.exp hm - 1) * s k at h
    nlinarith
  have hprod := hq (s k) (s (k + 1)) (hs2 k) (by linarith [hs (k + 1)]) hstep
  have hcoeff : (linearPoly (J k)).coeffNorm + (linearPoly (J k)⁻¹).coeffNorm ≤ K0 * s k ^ q := by
    have h₁ := linearPoly_coeffNorm_le_matOpNorm (J k)
    have h₂ := linearPoly_coeffNorm_le_matOpNorm (J k)⁻¹
    have hmul := mul_le_mul_of_nonneg_left hJ (sq_nonneg (n : ℝ))
    have hmul' := mul_le_mul_of_nonneg_left hprod hK0
    dsimp only [K0] at hmul' ⊢
    nlinarith
  have hpoly : s k ^ q ≤ Real.exp ((4 * |q|) * Real.sqrt (s k)) :=
    (Real.rpow_le_rpow (by linarith [hs k]) (by linarith : s k ≤ 1 + s k) hq0).trans
      (polynomial_le_sqrt_envelope (hs k))
  exact hcoeff.trans (mul_sqrt_envelope hK0 (Real.rpow_nonneg (by linarith [hs k]) _)
    (constant_le_sqrt_envelope hK0 (hs k)) hpoly)

end Yau.Proofs.Y01Aux
