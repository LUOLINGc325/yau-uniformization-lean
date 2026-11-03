import Mathlib

/-! The explicit source-coordinate variation has two holomorphic endpoint
germs and a freely prescribed quadratic correction at the terminal end. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Proofs.C03Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def movingTrial (γ W : ℝ → E) (Q : E) (t : ℝ) (a : ℂ) : E :=
  γ t + a • W t + (((t : ℂ) / 2) * a ^ 2) • Q

theorem movingTrial_zero_parameter (γ W : ℝ → E) (Q : E) (t : ℝ) :
    movingTrial γ W Q t 0 = γ t := by
  simp [movingTrial]

theorem movingTrial_initial (γ W : ℝ → E) (Q : E) (a : ℂ) :
    movingTrial γ W Q 0 a = γ 0 + a • W 0 := by
  simp [movingTrial]

theorem movingTrial_terminal (γ W : ℝ → E) (Q : E) (a : ℂ) :
    movingTrial γ W Q 1 a = γ 1 + a • W 1 + ((1 / 2 : ℂ) * a ^ 2) • Q := by
  simp [movingTrial]

theorem movingTrial_hasDerivAt (γ W : ℝ → E) (Q : E) (t : ℝ) (a : ℂ) :
    HasDerivAt (movingTrial γ W Q t) (W t + ((t : ℂ) * a) • Q) a := by
  have hp := ((hasDerivAt_pow 2 a).const_mul ((t : ℂ) / 2)).smul_const Q
  have hq := (((hasDerivAt_id a).smul_const (W t)).add hp).const_add (γ t)
  have he : ((t : ℂ) / 2) * ((2 : ℂ) * a ^ (2 - 1)) = (t : ℂ) * a := by ring
  change HasDerivAt (fun b : ℂ => γ t + b • W t + (((t : ℂ) / 2) * b ^ 2) • Q)
    (W t + ((t : ℂ) * a) • Q) a
  simpa only [Pi.add_apply, id_eq, Nat.cast_ofNat, he, one_smul, add_assoc] using hq

theorem movingTrial_deriv (γ W : ℝ → E) (Q : E) (t : ℝ) (a : ℂ) :
    deriv (movingTrial γ W Q t) a = W t + ((t : ℂ) * a) • Q :=
  (movingTrial_hasDerivAt γ W Q t a).deriv

theorem movingTrial_hasSecondDerivAt (γ W : ℝ → E) (Q : E) (t : ℝ) (a : ℂ) :
    HasDerivAt (deriv (movingTrial γ W Q t)) ((t : ℂ) • Q) a := by
  have hd : deriv (movingTrial γ W Q t) =
      fun b : ℂ => W t + ((t : ℂ) * b) • Q := by
    funext b
    exact movingTrial_deriv γ W Q t b
  rw [hd]
  simpa using (((hasDerivAt_id a).const_mul (t : ℂ)).smul_const Q).const_add (W t)

theorem movingTrial_differentiable (γ W : ℝ → E) (Q : E) (t : ℝ) :
    Differentiable ℂ (movingTrial γ W Q t) :=
  fun a => (movingTrial_hasDerivAt γ W Q t a).differentiableAt

theorem movingTrial_secondJet_terminal (γ W : ℝ → E) (Q : E) :
    deriv (deriv (movingTrial γ W Q 1)) 0 = Q := by
  simpa using (movingTrial_hasSecondDerivAt γ W Q 1 0).deriv

section RealSmooth
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem movingTrial_contDiffOn (γ W : ℝ → E) (Q : E) (J : Set ℝ)
    (hγ : ContDiffOn ℝ ∞ γ J) (hW : ContDiffOn ℝ ∞ W J) :
    ContDiffOn ℝ ∞ (Function.uncurry (movingTrial γ W Q)) (J ×ˢ Set.univ) := by
  have hγ' : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => γ p.1) (J ×ˢ Set.univ) :=
    hγ.comp contDiffOn_fst (fun _ hp => hp.1)
  have hW' : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1) (J ×ˢ Set.univ) :=
    hW.comp contDiffOn_fst (fun _ hp => hp.1)
  have ht : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1 : ℂ)) (J ×ˢ Set.univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_fst
  exact (hγ'.add (contDiffOn_snd.smul hW')).add
    (((ht.div_const 2).mul (contDiffOn_snd.pow 2)).smul_const Q)

end RealSmooth

end Yau.Proofs.C03Aux
