import Yau.LeafProofs.L05ABPRegularization
import Yau.LeafProofs.L05ViscosityPrimitives

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def abpSpaceRetract {n : ℕ} (x : Space n) : Space n := (max 1 ‖x‖)⁻¹ • x

def abpRetract {n : ℕ} (z : Point n) : Point n :=
  (abpSpaceRetract z.1,max (-1) (min 0 z.2))

theorem abpSpaceRetract_mem {n : ℕ} (x : Space n) :
    abpSpaceRetract x∈Metric.closedBall (0 : Space n) 1 := by
  rw [Metric.mem_closedBall,dist_zero_right,abpSpaceRetract,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))]
  have hh := le_max_right (1:ℝ) ‖x‖
  exact (inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖))).mpr (by simpa using hh)

theorem abpSpaceRetract_eq {n : ℕ} {x : Space n} (hx : x∈Metric.closedBall (0 : Space n) 1) :
    abpSpaceRetract x=x := by
  have hn : ‖x‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  simp only [abpSpaceRetract,max_eq_left hn,inv_one,one_smul]

theorem abpSpaceRetract_lipschitz (n : ℕ) : LipschitzWith 2 (abpSpaceRetract (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  let a := max 1 ‖x‖
  let b := max 1 ‖y‖
  have ha1 : 1≤a := le_max_left _ _
  have hb1 : 1≤b := le_max_left _ _
  have ha : 0<a := lt_of_lt_of_le zero_lt_one ha1
  have hb : 0<b := lt_of_lt_of_le zero_lt_one hb1
  have hx : ‖x‖≤a := le_max_right _ _
  have hy : ‖y‖≤b := le_max_right _ _
  have hab : |a-b|≤‖x-y‖ := by
    have hxy : ‖x‖≤‖y‖+‖x-y‖ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub x y (0 : Space n)
      simpa only [sub_zero,add_comm] using hh
    have hyx : ‖y‖≤‖x‖+‖x-y‖ := by
      have hh := norm_sub_le_norm_sub_add_norm_sub y x (0 : Space n)
      simpa only [sub_zero,norm_sub_rev y x,add_comm] using hh
    have ha' : a≤b+‖x-y‖ := max_le (by linarith [norm_nonneg (x-y)]) (by linarith)
    have hb' : b≤a+‖x-y‖ := max_le (by linarith [norm_nonneg (x-y)]) (by linarith)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : |a⁻¹-b⁻¹| * ‖y‖≤‖x-y‖ := by
    calc
      _ ≤ |a⁻¹-b⁻¹| * b := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ = |(a⁻¹-b⁻¹)*b| := by rw [abs_mul,abs_of_pos hb]
      _ = |(b-a)/a| := by congr 1; field_simp
      _ = |a-b|/a := by rw [abs_div,abs_of_pos ha,abs_sub_comm]
      _ ≤ |a-b| := div_le_self (abs_nonneg _) ha1
      _ ≤ ‖x-y‖ := hab
  have hinv : a⁻¹≤1 := (inv_le_one₀ ha).mpr ha1
  have he : abpSpaceRetract x-abpSpaceRetract y=a⁻¹ • (x-y)+(a⁻¹-b⁻¹) • y := by
    dsimp only [abpSpaceRetract,a,b]
    module
  rw [he]
  have hh := norm_add_le (a⁻¹ • (x-y)) ((a⁻¹-b⁻¹) • y)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)] at hh
  have hi := mul_le_mul_of_nonneg_right hinv (norm_nonneg (x-y))
  norm_num only [NNReal.coe_ofNat] at ⊢
  linarith

theorem abpRetract_mem {n : ℕ} (z : Point n) : abpRetract z∈unitClosed n := by
  refine ⟨abpSpaceRetract_mem z.1,le_max_left _ _,?_⟩
  exact max_le (by norm_num) (min_le_left _ _)

theorem abpRetract_eq {n : ℕ} {z : Point n} (hz : z∈unitClosed n) : abpRetract z=z := by
  apply Prod.ext
  · exact abpSpaceRetract_eq hz.1
  · change max (-1) (min 0 z.2)=z.2
    rw [min_eq_right hz.2.2,max_eq_right hz.2.1]

theorem abpRetract_uniformContinuous (n : ℕ) : UniformContinuous (abpRetract (n := n)) := by
  apply UniformContinuous.prodMk
  · exact (abpSpaceRetract_lipschitz n).uniformContinuous.comp uniformContinuous_fst
  · have hc : LipschitzWith 1 (fun t : ℝ => max (-1) (min 0 t)) :=
      (LipschitzWith.id.const_min 0).const_max (-1)
    exact hc.uniformContinuous.comp uniformContinuous_snd

theorem abp_bounded_uniform_extension {n : ℕ} {v : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) :
    ∃ f : Point n → ℝ, UniformContinuous f ∧ Set.EqOn f v (unitClosed n) ∧
      ∃ M : ℝ, 0<M ∧ ∀ z, |f z|≤M := by
  let f := v ∘ abpRetract
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have huc : UniformContinuous f := by
    apply uniformContinuousOn_univ.mp
    exact (hD.uniformContinuousOn_of_continuous hv).comp
      (abpRetract_uniformContinuous n).uniformContinuousOn (fun z _ => abpRetract_mem z)
  have hbound := (hD.image_of_continuousOn hv.norm).bddAbove
  obtain ⟨C,hC⟩ := hbound
  refine ⟨f,huc,?_,|C|+1,by positivity,?_⟩
  · intro z hz
    change v (abpRetract z)=v z
    rw [abpRetract_eq hz]
  · intro z
    have hh : |v (abpRetract z)|≤C := by
      simpa only [Function.comp_def,Real.norm_eq_abs] using
        hC (Set.mem_image_of_mem (fun z => ‖v z‖) (abpRetract_mem z))
    dsimp only [f,Function.comp_def]
    linarith [le_abs_self C]

end Yau.LeafProofs.L05Aux
