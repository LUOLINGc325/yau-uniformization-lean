import Yau.Proofs.F05BootstrapGoodDirections

/-! Every computed good derivative of a field with zero physical trace has
zero physical trace. Tangent lines and backward within-time derivatives use
only values on that actual face. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_partial_zero_face {ν d : Option (RIdx n)} {T : ℝ}
    {v : Point n → V} (hd : F05GoodLetter ν d) (hv : F05ZeroFace ν T v) :
    F05ZeroFace ν T (F05GoodPartial T d v) := by
  cases ν with
  | none => trivial
  | some j =>
    intro x hx hxj t ht
    cases d with
    | none =>
      change derivWithin (fun a => v (x,a)) (Ioc 0 T) t = 0
      have hEq : derivWithin (fun a => v (x,a)) (Ioc 0 T) t =
          derivWithin (fun _ : ℝ => (0 : V)) (Ioc 0 T) t :=
        derivWithin_congr (fun a ha => hv x hx hxj a ha) (hv x hx hxj t ht)
      rw [hEq,derivWithin_fun_const,Pi.zero_apply]
    | some k =>
      have hkj : k ≠ j := hd
      have hVec : realCoord (realVec k) j = 0 := by
        rw [← real_inner_realVec,realVec_inner,ite_eq_right hkj]
      have hNear : {a : ℝ | ‖x+a • realVec k‖ < 2} ∈ 𝓝 0 := by
        apply (isOpen_lt ((continuous_const.add
          (continuous_id.smul continuous_const)).norm) continuous_const).mem_nhds
        change ‖x+(0 : ℝ) • realVec k‖ < 2
        simpa only [Metric.mem_ball,dist_zero_right,zero_smul,add_zero] using hx
      have hEq : (fun a : ℝ => v (x+a • realVec k,t)) =ᶠ[𝓝 0]
          (fun _ : ℝ => (0 : V)) := by
        filter_upwards [hNear] with a ha
        apply hv (x+a • realVec k)
        · simpa only [Metric.mem_ball,dist_zero_right] using ha
        · rw [← realCoordLinear_apply,map_add,map_smul]
          simp only [realCoordLinear_apply,smul_eq_mul,hVec,hxj,mul_zero,add_zero]
        · exact ht
      change deriv (fun a : ℝ => v (x+a • realVec k,t)) 0 = 0
      rw [hEq.deriv_eq]
      simp only [deriv_const]

theorem F05_good_word_zero_face {ν : Option (RIdx n)} {T : ℝ}
    {v : Point n → V} (hv : F05ZeroFace ν T v) (β : List (Option (RIdx n)))
    (hβ : F05GoodList ν β) : F05ZeroFace ν T (F05GoodWord T β v) := by
  induction β with
  | nil => exact hv
  | cons d β ih =>
    have hdβ := (F05GoodList_cons ν d β).mp hβ
    exact F05_good_partial_zero_face hdβ.1 (ih hdβ.2)

end Yau.Proofs.F05Aux
