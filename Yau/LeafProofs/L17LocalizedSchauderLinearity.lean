import Yau.LeafProofs.L17LocalizedSchauderUniformAssembly

open Set
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem globalSum_eq_literal (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : Cylinder M T) :
    globalSum P T v q = ∑ᶠ (p : P.centers), if q.1 ∈ (P.charts.chart p).target then
      P.localization p q.1*v p ((P.charts.chart p).symm q.1,q.2) else 0 := by
  unfold globalSum
  congr 1
  funext p
  exact localizedTerm_eq_formula P T p (v p) q

theorem globalSum_add (P : UniformChartPartition g) (T : ℝ)
    (v w : P.centers → ComplexVector n × Time T → ℝ) :
    globalSum P T (fun p q => v p q+w p q) = globalSum P T v+globalSum P T w := by
  funext q
  have hh := supported_finsum_add P T (fun p => localizedTerm P T p (v p)) (fun p => localizedTerm P T p (w p))
    (fun p r hr => localizedTerm_zero_of_not_cover P T p (v p) r hr)
    (fun p r hr => localizedTerm_zero_of_not_cover P T p (w p) r hr) q
  simpa only [globalSum,localizedTerm,mul_add,Pi.add_apply] using hh

theorem globalSum_smul (P : UniformChartPartition g) (T : ℝ) (c : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) :
    globalSum P T (fun p q => c • v p q) = c • globalSum P T v := by
  funext q
  have hh := supported_finsum_smul P T (fun p => localizedTerm P T p (v p)) c
    (fun p r hr => localizedTerm_zero_of_not_cover P T p (v p) r hr) q
  simpa only [globalSum,localizedTerm,smul_eq_mul,mul_left_comm,Pi.smul_apply] using hh

theorem schauder_add_of_globalSum {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}
    (v w : P.centers → ComplexVector n × Time T → ℝ)
    (u₁ u₂ u₃ : SchauderSpace P T gamma hT)
    (h₁ : schauderFun u₁ = globalSum P T v) (h₂ : schauderFun u₂ = globalSum P T w)
    (h₃ : schauderFun u₃ = globalSum P T (fun p q => v p q+w p q)) : u₃ = u₁+u₂ := by
  apply schauderFun_injective
  have hAdd : schauderFun (u₁+u₂) = schauderFun u₁+schauderFun u₂ := by
    funext q
    change functionCLM P T gamma hT (u₁+u₂) q = _
    rw [map_add]
    rfl
  rw [h₃,hAdd,h₁,h₂,globalSum_add]

theorem schauder_smul_of_globalSum {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}
    (v : P.centers → ComplexVector n × Time T → ℝ) (c : ℝ)
    (u₁ u₂ : SchauderSpace P T gamma hT)
    (h₁ : schauderFun u₁ = globalSum P T v)
    (h₂ : schauderFun u₂ = globalSum P T (fun p q => c • v p q)) :
    u₂ = (c • u₁ : SchauderSpace P T gamma hT) := by
  apply schauderFun_injective
  have hSmul : schauderFun (c • u₁ : SchauderSpace P T gamma hT) = c • schauderFun u₁ := by
    funext q
    change functionCLM P T gamma hT (c • u₁) q = _
    rw [map_smul]
    rfl
  rw [h₂,hSmul,h₁,globalSum_smul]

end Yau.LeafProofs.L17LocalizedSchauderAux
