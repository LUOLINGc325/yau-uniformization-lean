import Yau.Proofs.Y06GeometricBudgetJump
import Yau.Proofs.Y06VolumeJetBounds
import Yau.Proofs.Y06NormalizedJet

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Yau.Proofs.Y06Aux.GeometricBudget
open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y01Aux Yau.Proofs.Y02Aux
open scoped ContDiff Matrix.Norms.L2Operator

namespace Envelope
variable {n : ℕ} {s : ℕ → ℝ} {reg : ℕ → Prop}

theorem linear {A : ℕ → Herm n} (hs : ∀ k, 1 ≤ s k)
    (hA : Envelope s reg (fun k => matOpNorm (A k))) :
    Envelope s reg (fun k => (linearPolynomial (A k)).coeffNorm) := by
  apply ((Envelope.constant hs ((n:ℝ)^2)).mul (fun _ => sq_nonneg _)
    (fun _ => norm_nonneg _) hA).mono
  intro k hk
  exact linearPoly_coeffNorm_le_matOpNorm _

theorem comp {P R : ℕ → PolyMap n} {d : ℕ} (hs : ∀ k, 1 ≤ s k)
    (hdeg : ∀ k, reg k → (P k).degree ≤ d)
    (hP : Envelope s reg (fun k => (P k).coeffNorm))
    (hR : Envelope s reg (fun k => (R k).coeffNorm)) :
    Envelope s reg (fun k => ((P k).comp (R k)).coeffNorm) := by
  obtain ⟨A,hA,hP⟩ := hP
  obtain ⟨B,hB,hR⟩ := hR
  exact ⟨A+d*(max 0 B+Real.log 2),by positivity,fun k hk =>
    comp_sqrt_envelope (hs k) (hdeg k hk) (hP k hk) (hR k hk)⟩

theorem choose_larger {f : ℕ → ℝ} (h : Envelope s reg f) {A B : ℝ}
    (hf : ∀ k, reg k → f k ≤ Real.exp (A*Real.sqrt (s k))) (hAB : A ≤ B) :
    ∀ k, reg k → f k ≤ Real.exp (B*Real.sqrt (s k)) := by
  intro k hk
  exact (hf k hk).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hAB (Real.sqrt_nonneg _)))

end Envelope

variable {n d : ℕ} {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

 theorem macro_bound_envelope (hhm : 0 < hm) {reg : ℕ → Prop} {f : ℕ → ℝ}
    (h : MacroBound (macroAt Q N M hm j₀) reg f) :
    Envelope (gridClock Q N M hm j₀)
      (fun k => reg k ∧ 1 ≤ macroAt Q N M hm j₀ k) f := by
  obtain ⟨C,hC,h⟩ := h
  apply (macro_power_envelope hhm hC).mono
  intro k hk
  exact h k hk.1 hk.2

 theorem volume_polynomial_envelope
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Q N M hm j₀) d r last logs B ell Evol A Ainv V)
    (hF : ∀ k, F (tk k) (tk (k+1)) 0 = 0 ∧ DifferentiableOn ℂ (F (tk k) (tk (k+1))) (Metric.ball 0 r))
    (hjets : ∀ m ≤ d, ∃ C : ℝ, ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      jetNorm (F (tk k) (tk (k+1))) m ≤ (1+gridClock Q N M hm j₀ k)^C) :
    Envelope (gridClock Q N M hm j₀)
      (fun k => Regular Q N M (macroAt Q N M hm j₀ k)) (fun k => (V k).coeffNorm) := by
  let s := gridClock Q N M hm j₀
  let reg := fun k => Regular Q N M (macroAt Q N M hm j₀ k)
  have hs : ∀ k, 1 ≤ s k := clock_one_le hhm
  obtain ⟨Cv,hCv,hv⟩ := hVol.2.2.2.2
  have hAk (k : ℕ) : (A k).coeffNorm ≤ (1+s k)^Cv := by
    have h := hv k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at h
    have he : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ := by positivity
    linarith [coeffNorm_nonneg (Ainv k)]
  have hIk (k : ℕ) : (Ainv k).coeffNorm ≤ (1+s k)^Cv := by
    have h := hv k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at h
    have he : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ := by positivity
    linarith [coeffNorm_nonneg (A k)]
  have hA : Envelope s reg (fun k => (A (k+1)).coeffNorm) := by
    refine ⟨(4*|Cv|)*Real.sqrt (Real.exp hm),by positivity,?_⟩
    intro k hk
    obtain ⟨ch,Ch,hch,hCh,hstep⟩ := hgrid.2.2.2.2.2
    exact next_sqrt_envelope (by positivity) (by linarith [hs k]) (hstep k).2.1
      ((hAk (k+1)).trans (polynomial_le_sqrt_envelope (hs (k+1))))
  have hI : Envelope s reg (fun k => (Ainv k).coeffNorm) :=
    (Envelope.polynomial hs Cv).mono (fun k _ => hIk k)
  obtain ⟨CF,hCF⟩ := hjets d le_rfl
  have hFj : Envelope s reg (fun k => jetNorm (F (tk k) (tk (k+1))) d) :=
    (Envelope.polynomial hs CF).mono hCF
  let p := partitionJetConstant d
  let q := cauchyJetConstant d
  have hp : 0 ≤ p := partitionConstant_nonneg d
  have hq : 0 ≤ q := cauchyConstant_nonneg d
  have hqI0 (k : ℕ) : 0 ≤ q*(Ainv k).coeffNorm := mul_nonneg hq (coeffNorm_nonneg _)
  have hIpow0 (k : ℕ) : 0 ≤ (1+q*(Ainv k).coeffNorm)^d :=
    pow_nonneg (add_nonneg zero_le_one (hqI0 k)) d
  have hpF0 (k : ℕ) : 0 ≤ p*jetNorm (F (tk k) (tk (k+1))) d :=
    mul_nonneg hp (jetNorm_nonneg _ _)
  have hinner0 (k : ℕ) : 0 ≤ (1+p*jetNorm (F (tk k) (tk (k+1))) d*(1+q*(Ainv k).coeffNorm)^d)^d :=
    pow_nonneg (add_nonneg zero_le_one (mul_nonneg (hpF0 k) (hIpow0 k))) d
  have hqA0 (k : ℕ) : 0 ≤ q*(A (k+1)).coeffNorm := mul_nonneg hq (coeffNorm_nonneg _)
  have hpqA0 (k : ℕ) : 0 ≤ p*(q*(A (k+1)).coeffNorm) := mul_nonneg hp (hqA0 k)
  have hqI := (Envelope.constant (reg := reg) hs q).mul (fun _ => hq)
    (fun _ => coeffNorm_nonneg _) hI
  have hIpow := ((Envelope.constant hs 1).add hs hqI).pow
    (fun k => add_nonneg zero_le_one (hqI0 k)) d
  have hpF := (Envelope.constant hs p).mul (fun _ => hp) (fun _ => jetNorm_nonneg _ _) hFj
  have hinner := ((Envelope.constant hs 1).add hs
    (hpF.mul hpF0 hIpow0 hIpow)).pow
    (fun k => add_nonneg zero_le_one (mul_nonneg (hpF0 k) (hIpow0 k))) d
  have hqA := (Envelope.constant hs q).mul (fun _ => hq) (fun _ => coeffNorm_nonneg _) hA
  have hpqA := (Envelope.constant hs p).mul (fun _ => hp) hqA0 hqA
  have hfull := hpqA.mul hpqA0 hinner0 hinner
  have hfinal := (Envelope.constant hs ((n:ℝ)*((boundedMonomials n d).card:ℝ))).mul
    (fun _ => by positivity) (fun k => mul_nonneg (hpqA0 k) (hinner0 k)) hfull
  apply hfinal.mono
  intro k hk
  obtain ⟨hellD,hell0,hellSum,hellJet,hED,hEJet,hAdef,hA0,hI0,hAlin,hAD,hID,hAleft,hAright,hVD,hVCV,hVjet⟩ := hVol.2.2.2.1 k
  exact volume_transition_coefficient_bound
    ((holomorphic_ball_smooth hVol.1 (hF k).2).of_le (WithTop.coe_le_coe.mpr le_top))
    (hF k).1 hI0 le_rfl hVD hVjet

end Yau.Proofs.Y06Aux.GeometricBudget
