import Yau.Proofs.Y06GeometricBudgetCoefficients

/-! Uniform geometric data for the finite homological problems. All constants
are chosen from the original geometric input before any finite mask or horizon. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Yau.Proofs.Y06Aux.GeometricBudget
open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof

variable {n d : ℕ}

 theorem geometric_budget
    (hn : 0 < n) {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps b : ℝ}
    (hhm : 0 < hm) (hb : 0 < b) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n} {L : Changes n}
    (hF : ∀ k, F (tk k) (tk (k+1)) 0 = 0 ∧ DifferentiableOn ℂ (F (tk k) (tk (k+1))) (Metric.ball 0 r))
    (hVol : CoherentVolume F tk (gridClock Q N M hm j₀) d r last logs B ell Evol A Ainv V)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k+1)) 0‖ =
      Real.exp (-(gridClock Q N M hm j₀ (k+1)-gridClock Q N M hm j₀ k)/2))
    (hChanges : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
        (macroAt Q N M hm j₀) (macroClock hm) C c L k ∧
      (Regular Q N M (macroAt Q N M hm j₀ (k+1)) →
        JumpAt E (weight Q N M hm scale K eps j₀ (rate F tk E)) L k))
    (hjets : ∀ m ≤ d, ∃ C : ℝ, ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      jetNorm (F (tk k) (tk (k+1))) m ≤ (1+gridClock Q N M hm j₀ k)^C) :
    let s := gridClock Q N M hm j₀
    let j := macroAt Q N M hm j₀
    let reg := fun k => Regular Q N M (j k)
    let w := weight Q N M hm scale K eps j₀ (rate F tk E)
    let D := diagonal F tk E
    let J := fun k => if reg (k+1) then alignedJump E L k else 1
    let P := normalizedPolynomial V E L
    ∃ k₀ : ℕ, ∃ A CT c : ℝ, (n+1:ℝ) ≤ A ∧ 0 ≤ CT ∧ 0 < c ∧
      (∀ k, k₀ ≤ k → reg k →
        1+(P k).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
        1+(linearPolynomial (J k)).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
        1+(linearPolynomial (J k)⁻¹).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
        1+(linearPolynomial (D k)).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
        1+(linearPolynomial (D k)⁻¹).coeffNorm ≤ Real.exp (A*Real.sqrt (s k)) ∧
        1+(PolyMap.id:PolyMap n).coeffNorm ≤ Real.exp (A*Real.sqrt (s k))) ∧
      (∀ m, 2 ≤ m → m ≤ d → ∀ k, k₀ ≤ k → reg k → ∀ X : PolyMap n,
        Homogeneous X m → (backwardOperator (D k) (J k) (w k) X).coeffNorm ≤
          (1+(j k:ℝ))^CT*Real.exp (-c*Real.sqrt (s k)/(j k:ℝ)^2)*X.coeffNorm) ∧
      (∀ k, reg k → IsUnit (J k)) := by
  dsimp only
  obtain ⟨C,c,hC,hc,hChanges⟩ := hChanges
  have hL k hk := (hChanges k hk).1
  obtain ⟨A,hA,hbound⟩ := regular_coefficient_budget hhm hgrid hE hVol hF hdet hjets hC.le hc hL
  obtain ⟨CT,cT,hCT,hcT,hT⟩ := uniform_backward_budget (d := d) hn hb hgrid hE hdet hweights hC.le hc hL
  let k₀ := offset Q N M hm j₀ (j₀+1)
  have hlate (k : ℕ) (hk : k₀ ≤ k) : 1 ≤ macroAt Q N M hm j₀ k := by
    have hmem := macroAt_mem Q N M hm j₀ k
    by_contra h
    have hz : macroAt Q N M hm j₀ k = 0 := by omega
    have hjz : j₀ = 0 := by omega
    have hbad : k < k₀ := by
      have ht := hmem.2
      rw [hz] at ht
      simpa only [k₀,hjz] using ht
    omega
  refine ⟨k₀,A,CT,cT,hA,hCT,hcT,?_,?_,?_⟩
  · intro k hk hreg
    exact hbound k hreg (hlate k hk)
  · intro m hm2 hmd k hk hreg X hX
    exact hT m hm2 hmd k hreg (hlate k hk) X hX
  · exact regular_jump_isUnit hE hL

end Yau.Proofs.Y06Aux.GeometricBudget
