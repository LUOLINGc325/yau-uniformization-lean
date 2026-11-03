import Yau.Proofs.Y06GeometricBudgetEnvelopes

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Yau.Proofs.Y06Aux.GeometricBudget
open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y01Aux Yau.Proofs.Y02Aux
open scoped Matrix.Norms.L2Operator

namespace Envelope
variable {s : ℕ → ℝ} {reg reg' : ℕ → Prop} {f : ℕ → ℝ}
theorem restrict (h : Envelope s reg f) (hh : ∀ k, reg' k → reg k) : Envelope s reg' f := by
  obtain ⟨A,hA,h⟩ := h
  exact ⟨A,hA,fun k hk => h k (hh k hk)⟩
end Envelope

variable {n d : ℕ} {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

theorem normalized_polynomial_envelope
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Q N M hm j₀) d r last logs B ell Evol A Ainv V)
    (hF : ∀ k, F (tk k) (tk (k+1)) 0 = 0 ∧ DifferentiableOn ℂ (F (tk k) (tk (k+1))) (Metric.ball 0 r))
    (hjets : ∀ m ≤ d, ∃ C : ℝ, ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      jetNorm (F (tk k) (tk (k+1))) m ≤ (1+gridClock Q N M hm j₀ k)^C)
    {L : Changes n} {w : ℕ → Fin n → ℝ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) w (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    Envelope (gridClock Q N M hm j₀) (fun k => Regular Q N M (macroAt Q N M hm j₀ k))
      (fun k => (normalizedPolynomial V E L k).coeffNorm) := by
  let s := gridClock Q N M hm j₀
  let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
  have hs : ∀ k, 1 ≤ s k := clock_one_le hhm
  have hmacro := macro_power_envelope (Q := Q) (N := N) (M := M) (j₀ := j₀) (reg := reg) hhm hC
  have hplus : Envelope s reg (fun k => matOpNorm (L.plus k)) := by
    apply hmacro.mono
    intro k hk
    have h := (hL k hk).2.2.2.2.1
    linarith [show 0 ≤ matOpNorm (L.plus k)⁻¹ from norm_nonneg _]
  have hminus : Envelope s reg (fun k => matOpNorm (L.minus k)⁻¹) := by
    have ht := ((Envelope.constant hs 2).add hs hmacro).pow (fun _ => by positivity) (n+1)
    apply ((Envelope.constant hs (n+1:ℝ)).mul (fun _ => by positivity) (fun _ => by positivity) ht).mono
    intro k hk
    have h := minus_change_polynomial_bound hE hc (hL k hk)
    have hnorm : 0 ≤ matOpNorm (L.minus k) := norm_nonneg _
    change matOpNorm (L.minus k)⁻¹ ≤ (n+1:ℝ)*(2+(1+(macroAt Q N M hm j₀ k:ℝ))^C)^(n+1)
    rw [add_comm 2]
    linarith
  have hRplus : Envelope s reg (fun k => (linearPolynomial (L.plus k*(E.finish k).conjTranspose)).coeffNorm) := by
    apply Envelope.linear hs
    apply hplus.mono
    intro k hk
    rw [matOpNorm_mul_unitary (Yau.Blueprint.Alignment.Y03Proof.unitary_conjTranspose (hE k).2.2.2.1)]
  have hRminus : Envelope s reg (fun k => (linearPolynomial (E.start k*(L.minus k)⁻¹)).coeffNorm) := by
    apply Envelope.linear hs
    apply hminus.mono
    intro k hk
    rw [matOpNorm_unitary_mul (hE k).2.2.1]
  have hV := volume_polynomial_envelope hhm hgrid hVol hF hjets
  have hVD (k : ℕ) : (V k).degree ≤ d := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hVD,_,_⟩ := hVol.2.2.2.1 k
    exact hVD
  have hinner := hV.comp hs (fun k _ => hVD k) hRminus
  exact hRplus.comp hs (fun k _ => linearPoly_degree_le _) hinner

 theorem regular_coefficient_budget
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Q N M hm j₀) d r last logs B ell Evol A Ainv V)
    (hF : ∀ k, F (tk k) (tk (k+1)) 0 = 0 ∧ DifferentiableOn ℂ (F (tk k) (tk (k+1))) (Metric.ball 0 r))
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k+1)) 0‖ =
      Real.exp (-(gridClock Q N M hm j₀ (k+1)-gridClock Q N M hm j₀ k)/2))
    (hjets : ∀ m ≤ d, ∃ C : ℝ, ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      jetNorm (F (tk k) (tk (k+1))) m ≤ (1+gridClock Q N M hm j₀ k)^C)
    {L : Changes n} {w : ℕ → Fin n → ℝ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) w (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    let s := gridClock Q N M hm j₀
    let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
    let J := fun k => if reg (k+1) then alignedJump E L k else 1
    ∃ A : ℝ, (n+1:ℝ) ≤ A ∧ ∀ k, reg k → 1 ≤ macroAt Q N M hm j₀ k →
      1+(normalizedPolynomial V E L k).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
      1+(linearPolynomial (J k)).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
      1+(linearPolynomial (J k)⁻¹).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
      1+(linearPolynomial (diagonal F tk E k)).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
      1+(linearPolynomial (diagonal F tk E k)⁻¹).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
      1+(PolyMap.id:PolyMap n).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) := by
  dsimp only
  let s := gridClock Q N M hm j₀
  let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
  let late := fun k => reg k ∧ 1 ≤ macroAt Q N M hm j₀ k
  let J := fun k => if reg (k+1) then alignedJump E L k else 1
  have hs : ∀ k, 1 ≤ s k := clock_one_le hhm
  have hP := (normalized_polynomial_envelope hhm hgrid hE hVol hF hjets hC hc hL).restrict (reg' := late) (fun _ h => h.1)
  have hnorm := macro_bound_envelope hhm (regular_jump_macro_bound hE hC hc hL)
  have hJ : Envelope s late (fun k => (linearPolynomial (J k)).coeffNorm) := by
    apply Envelope.linear hs
    exact hnorm.mono (fun k _ => by dsimp only; exact le_add_of_nonneg_right (show 0 ≤ matOpNorm (J k)⁻¹ from norm_nonneg _))
  have hJi : Envelope s late (fun k => (linearPolynomial (J k)⁻¹).coeffNorm) := by
    apply Envelope.linear hs
    exact hnorm.mono (fun k _ => by dsimp only; exact le_add_of_nonneg_left (show 0 ≤ matOpNorm (J k) from norm_nonneg _))
  have hD : Envelope s late (fun k => (linearPolynomial (diagonal F tk E k)).coeffNorm) := by
    apply Envelope.linear hs
    apply (Envelope.constant hs 1).mono
    intro k hk
    change ‖Matrix.diagonal (fun i => (singularLength F tk E k i:ℂ))‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((hE k).2.2.2.2.2.1 i).1]
    exact ((hE k).2.2.2.2.2.1 i).2
  have hDi : Envelope s late (fun k => (linearPolynomial (diagonal F tk E k)⁻¹).coeffNorm) := by
    apply Envelope.linear hs
    obtain ⟨ch,Ch,hch,hCh,hstep⟩ := hgrid.2.2.2.2.2
    refine ⟨Ch/2,by positivity,?_⟩
    intro k hk
    apply (diagonal_inverse_clock_bound hE hdet k).trans
    apply Real.exp_le_exp.mpr
    have h := (hstep k).2.2 hk.1
    dsimp only [s] at *
    linarith
  have hId : Envelope s late (fun _ => (PolyMap.id:PolyMap n).coeffNorm) := Envelope.constant hs _
  have hsum := (((((hP.add hs hJ).add hs hJi).add hs hD).add hs hDi).add hs hId)
  have hone := (Envelope.constant (reg := late) hs 1).add hs hsum
  obtain ⟨A0,hA0,hbound⟩ := hone
  refine ⟨max (n+1:ℝ) A0,le_max_left _ _,?_⟩
  intro k hk hj
  have hh := (hbound k ⟨hk,hj⟩).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (le_max_right (n+1:ℝ) A0) (Real.sqrt_nonneg (s k))))
  have h₁ := coeffNorm_nonneg (normalizedPolynomial V E L k)
  have h₂ := coeffNorm_nonneg (linearPolynomial (J k))
  have h₃ := coeffNorm_nonneg (linearPolynomial (J k)⁻¹)
  have h₄ := coeffNorm_nonneg (linearPolynomial (diagonal F tk E k))
  have h₅ := coeffNorm_nonneg (linearPolynomial (diagonal F tk E k)⁻¹)
  have h₆ := coeffNorm_nonneg (PolyMap.id:PolyMap n)
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

end Yau.Proofs.Y06Aux.GeometricBudget
