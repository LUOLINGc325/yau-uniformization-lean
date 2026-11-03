import Yau.LeafProofs.L16DomainDataLow

/-! The actual compatible source obtained from the frozen Schauder boundary data. -/

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance domainDataSource_dualGroup {n : ℕ} :
    NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance domainDataSource_dualSpace {n : ℕ} :
    NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance domainDataSource_hessianGroup {n : ℕ} :
    NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance domainDataSource_hessianSpace {n : ℕ} :
    NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The original Schauder data norm controls its actual differential operator.
    The constant precedes both coefficients and data; no lower-jet Holder
    premise or additional differentiability is imposed on the datum. -/
theorem smoothDomain_linearOp_data_holder {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {α T M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
      (u : Point n → ℝ) P,
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      SchauderBound α (cylinder (closure O) 0 T) u P →
      HolderBound α (cylinder (closure O) 0 T)
        (linearOp (cylinder (closure O) 0 T) a b u) (C*P) := by
  classical
  obtain ⟨D,hD,hLow⟩ := smoothDomain_data_lowPair_holder hO hα hα1 hT
  let N : ℝ := Fintype.card (Yau.RIdx n)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨1+2*N^2*M+2*N*M*D,by positivity,?_⟩
  intro a b u P ha hb hu
  have hPrincipal := hessian_contraction_holderBound hM hu.2.1
    (fun i j => holderBound_matrix_entry ha i j)
    (fun i j p hp => (frobenius_entry_abs_le (a p) i j).trans (ha.2.1 p hp))
    hu.2.2.2.1 hu.2.2.2.1.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
    holderBound_mul (hb i) (holderBound_gradient_component (holderBound_snd (hLow u P hu)) i))
  have h := holderBound_sub (holderBound_sub hu.2.2.2.2 hPrincipal) hDrift
  convert h using 1 <;> simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  · rfl
  · dsimp only [N]
    ring

/-- Subtracting the actual operator of the frozen boundary datum yields a
    Holder source with precisely the corner condition of `Compatible`. -/
theorem smoothDomain_compatible_source_holder {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {α T M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
      (f p : Point n → ℝ) F P,
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun z => b z i) M) →
      HolderBound α (cylinder (closure O) 0 T) f F →
      SchauderBound α (cylinder (closure O) 0 T) p P →
      Compatible O T a b f p →
      HolderBound α (cylinder (closure O) 0 T)
        (fun z => f z-linearOp (cylinder (closure O) 0 T) a b p z) (C*(F+P)) ∧
      ∀ x ∈ frontier O, f (x,0)-linearOp (cylinder (closure O) 0 T) a b p (x,0) = 0 := by
  obtain ⟨D,hD,hOp⟩ := smoothDomain_linearOp_data_holder hO hα hα1 hT hM
  refine ⟨1+D,by positivity,?_⟩
  intro a b f p F P ha hb hf hp hCompatible
  refine ⟨holderBound_mono_const (holderBound_sub hf (hOp a b p P ha hb hp)) ?_,?_⟩
  · nlinarith [hf.1,hp.2.1]
  · intro x hx
    exact sub_eq_zero.mpr (hCompatible x hx).symm

end Yau.LeafProofs.L16Aux
