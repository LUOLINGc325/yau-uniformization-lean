import Yau.LeafProofs.L05AutonomousTimeIncrementsDerivative

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_second_derivative_parametric {a b d s : ℝ} (hd : 0 < d) (hab : a+d < b)
    (hs : 1 < s) (hs2 : s < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A : ℝ, 0 ≤ M → 0 ≤ A →
      ∀ (X : Type*) [TopologicalSpace X] (K : Set X) (f : X × ℝ → ℝ),
      ContinuousOn f (K ×ˢ Icc a b) →
      (∀ x∈K, ∀ t∈Icc a b, |f (x,t)| ≤ M) →
      (∀ x∈K, ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b →
        |autoRealSecond (fun tau => f (x,tau)) t h| ≤ A*h^s) →
      ∃ V : X × ℝ → ℝ, ContinuousOn V (K ×ˢ Icc (a+d) b) ∧
        ∀ x∈K, ContinuousOn (fun t => V (x,t)) (Icc (a+d) b) ∧
        (∀ t∈Icc (a+d) b, |V (x,t)| ≤ C*(M+A)) ∧
        (∀ t∈Icc (a+d) b, ∀ u∈Icc (a+d) b, |V (x,t)-V (x,u)| ≤ C*A*|t-u|^(s-1)) ∧
        (∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
          |(f (x,t)-f (x,t-h))/h-V (x,t)| ≤ C*A*h^(s-1)) ∧
        (∀ t∈Icc (a+d) b, ∀ u∈Icc (a+d) b, f (x,u)-f (x,t)=∫ tau in t..u, V (x,tau)) ∧
        (∀ t∈Ioo (a+d) b, HasDerivAt (fun tau => f (x,tau)) (V (x,t)) t) ∧
        (∀ t∈Icc (a+d) b, HasDerivWithinAt (fun tau => f (x,tau)) (V (x,t)) (Icc (a+d) b) t) := by
  classical
  obtain ⟨C,hC,hScalar⟩ := auto_second_derivative hd hab hs hs2
  refine ⟨C,hC,?_⟩
  intro M A hM hA X _inst K f hf hBound hSecond
  have hSlices (x : {x : X // x∈K}) := hScalar M A hM hA (fun t => f (x.val,t))
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨x.property,ht⟩))
    (hBound x.val x.property) (hSecond x.val x.property)
  choose W hW using hSlices
  let V : X × ℝ → ℝ := fun z => if hz : z.1∈K then W ⟨z.1,hz⟩ z.2 else 0
  have hError (k : ℕ) (z : X × ℝ) (hz : z∈K ×ˢ Icc (a+d) b) :
      |autoBackwardSlope (fun t => f (z.1,t)) z.2 (autoDyadicStep (d/2) k)-V z| ≤
        (C*A*(d/2)^(s-1))*((1/2 : ℝ)^(s-1))^k := by
    have h := (hW ⟨z.1,hz.1⟩).2.2.2.1 z.2 hz.2 (autoDyadicStep (d/2) k)
      (auto_dyadicStep_pos (half_pos hd) k) (auto_dyadicStep_le (half_pos hd).le k)
    rw [auto_dyadicStep_rpow (half_pos hd).le] at h
    simpa only [V,dite_eq_left hz.1,autoBackwardSlope,mul_assoc] using h
  have hUniform := auto_uniform_limit_of_geometric_error
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (s-1))
    (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) (by linarith : 0 < s-1)) hError
  have hCont (k : ℕ) : ContinuousOn (fun z : X × ℝ =>
      autoBackwardSlope (fun t => f (z.1,t)) z.2 (autoDyadicStep (d/2) k)) (K ×ˢ Icc (a+d) b) := by
    let h := autoDyadicStep (d/2) k
    have hPos : 0 < h := auto_dyadicStep_pos (half_pos hd) k
    have hLe : h ≤ d/2 := auto_dyadicStep_le (half_pos hd).le k
    have hOrig : ContinuousOn f (K ×ˢ Icc (a+d) b) := hf.mono (fun z hz =>
      ⟨hz.1,by linarith [hz.2.1],hz.2.2⟩)
    have hTrans : ContinuousOn (fun z : X × ℝ => f (z.1,z.2-h)) (K ×ˢ Icc (a+d) b) :=
      hf.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
        (fun z hz => ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩)
    exact (hOrig.sub hTrans).div_const h
  refine ⟨V,hUniform.continuousOn (Eventually.of_forall hCont).frequently,?_⟩
  intro x hx
  simpa only [V,dite_eq_left hx] using hW ⟨x,hx⟩

end Yau.LeafProofs.L05AutonomousAux
