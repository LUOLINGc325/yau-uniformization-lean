import Yau.Proofs.F05HolderLogModulus
import Yau.Proofs.F05HolderModelOscillation
import Yau.Proofs.F05HolderPairGluing

/-! Boundary Hölder control on a physical model chart, with no trace datum
on the artificial rim and no quantitative derivative bound on q. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_exp_model_holder_from_core (k : Option (RIdx n)) {S lam upper m B γ Cdg : ℝ}
    (hS : 0 < S) (hm : 0 < m) (hmB : m ≤ B)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hCdg : 0 < Cdg)
    (hCore : InteriorOscillationEstimate n (lam/B) (upper/m) γ Cdg)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R p : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 2) 0 S) a lam upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ S →
      ∀ q : Point n → ℝ,
      C2 (cylinder (region k 2) 0 T) q →
      ContDiffOn ℝ ∞ q (F05CapOpen k 3 ×ˢ Ioc 0 T) →
      (∀ z ∈ cylinder (region k 2) 0 T, m ≤ q z ∧ q z ≤ B) →
      (∀ x ∈ region k 2, q (x,0) = p (x,0)) →
      (∀ x ∈ frontier (F05FlatOpen k) ∩ Metric.ball 0 2,
        ∀ t ∈ Icc 0 T, q (x,t) = p (x,t)) →
      ExpDivergenceEquation (F05CapOpen k 3 ×ˢ Ioc 0 T) a b R q →
      HolderBound γ (cylinder (region k (3/2)) 0 T) q C := by
  obtain ⟨ℓ,A₁,b₁,H,W₀,E,L,hA₁,hb₁,hH,hW₀,hE,hL,hDataLip,hControl⟩ :=
    F05_log_model_control k hm hmB hab hR hp he
  have hν := (expDivergence_ellipticity_constants he hm hmB).1
  obtain ⟨K,hK,hError⟩ := F05_buffered_error_of_log_control k hν hA₁.le hb₁.le hH hW₀ hE
  obtain ⟨F,ρ,hF,hρ,hρsmall,hOsc⟩ := F05_exp_model_oscillation k hm hmB hCore hab hR he
  obtain ⟨C,hC,hHolder⟩ := F05_buffered_holder_from_error_and_interior k
    (hm.trans_le hmB).le hK.le hL.le hγ hγ1 hCdg.le hF.le hρ hρsmall
  refine ⟨C,hC,?_⟩
  intro T hT hTS q hq hqSmooth hbound hi hl heq
  obtain ⟨hLog,hTransfer⟩ := hControl T hT hTS q hq hbound hi hl heq
  have hErrorActual := hError T hT (fun z => (q z)⁻¹ • a z) (fun z j => b z j/q z)
    (fun z => Real.log (q z)-ℓ (p z)) q (fun z => Real.exp (ℓ (p z))) hLog hTransfer
  have hWide : cylinder (region k (7/4)) 0 T ⊆
      cylinder (Metric.closedBall (0 : Space n) 2) 0 S := by
    intro z hz
    refine ⟨?_,hz.2.1,hz.2.2.trans hTS⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith [hz.1.1]
  apply hHolder T hT q (fun z => Real.exp (ℓ (p z)))
    (fun z hz => by rw [abs_of_pos (hm.trans_le (hbound z hz).1)]; exact (hbound z hz).2)
    hErrorActual
    (fun z hz w hw => hDataLip z (hWide hz) w (hWide hw))
    (hOsc T hT hTS q hq hqSmooth hbound heq)

end Yau.Proofs.F05Aux
