import Yau.LeafProofs.L23BernsteinStep
import Yau.LeafProofs.L23BernsteinConstants
import Yau.LeafProofs.L23ContractionWords

/-! A lower time buffer gives a single numerical Bernstein constant. -/

noncomputable section
namespace Yau.LeafProofs.L23Aux

theorem bernsteinScalarBound_time_formula (σ B Dk Ek δ G L : ℝ)
    (hσ : 0 < σ) (hB : 0 < B) (hδ : 0 < δ) :
    bernsteinScalarBound σ B Dk Ek δ G L=
      (2/(σ*(1/(4*(17*B)^2))*δ)+2*(L+σ*G)/(σ*(1/(4*(17*B)^2)))+
        Real.sqrt (2*((17*B*Dk+Ek)^2+17*B*Dk)/(1/(4*(17*B)^2))))/(16*B) := by
  unfold bernsteinScalarBound
  field_simp

theorem bernsteinScalarBound_antitone_time (σ B Dk Ek G L δ₀ δ : ℝ)
    (hσ : 0 < σ) (hB : 0 < B) (hδ₀ : 0 < δ₀) (hδ : δ₀ ≤ δ) :
    bernsteinScalarBound σ B Dk Ek δ G L≤bernsteinScalarBound σ B Dk Ek δ₀ G L := by
  have hδpos := hδ₀.trans_le hδ
  rw [bernsteinScalarBound_time_formula σ B Dk Ek δ G L hσ hB hδpos,
    bernsteinScalarBound_time_formula σ B Dk Ek δ₀ G L hσ hB hδ₀]
  have hα : 0 < 1/(4*(17*B)^2) := by positivity
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr

theorem bernsteinScalarBound_le_stepBound (n k : ℕ) (K σ R δ B : ℝ)
    (hσ : 0 < σ) (hB : 0 < B) (hδ : 0 < δ) :
    bernsteinScalarBound σ B (jetEvolutionConstant n k*(k+1 : ℕ)*B)
      (jetEvolutionConstant n (k-1)*k*B^2) δ (16/R^2)
      (σ*(2*(2*n : ℕ)/R^2+(8/3 : ℝ)*(2*n : ℕ)*K))≤
        bernsteinStepBound n k K σ R δ B (jetEvolutionConstant n k) (jetEvolutionConstant n (k-1)) := by
  unfold bernsteinScalarBound bernsteinStepBound
  simp only [Nat.cast_add,Nat.cast_one]
  linarith

end Yau.LeafProofs.L23Aux
