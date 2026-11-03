import Yau.LeafProofs.L23DistanceCutoffBernstein
import Yau.LeafProofs.L23DerivativeNumericBounds
import Yau.LeafProofs.L23JetClosedEndpoint

/-! The complete jet induction, consuming only the local distance support construction. -/

noncomputable section
open scoped Topology
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n : ℕ} {M : ComplexManifold n}

def DerivativeCutoffSupports (h : ℝ → HermitianField M) (p : M.Carrier)
    (a K r τ σ : ℝ) : Prop :=
  ∀ k : ℕ, ∀ q∈distBall (h a) p (derivativeRadius r (k+1)), ∀ b₀ T : ℝ,
    a≤b₀ → b₀<T → T<a+2*τ →
    ParabolicCutoffLowerSupports h σ (timeDistanceCutoff h q (derivativeCutoffRadius n K r τ σ (k+1)))
      (fieldDistanceBuffer (h a) p (derivativeRadius r (k+1)) (derivativeRadius r k)) b₀ T
      (16/(derivativeCutoffRadius n K r τ σ (k+1))^2)
      (σ*(2*(2*n : ℕ)/(derivativeCutoffRadius n K r τ σ (k+1))^2+
        (8/3 : ℝ)*(2*n : ℕ)*K))

theorem jetSq_nested_bound_of_cutoffSupports
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x∈distBall (h a) p (2*r), ∀ t∈Set.Icc a (a+2*τ), curvatureJetNorm (h t) 0 x≤K)
    (hSupports : DerivativeCutoffSupports h p a K r τ σ) (k : ℕ) :
    ∀ x∈distBall (h a) p (derivativeRadius r k),
      ∀ t∈Set.Ico (a+derivativeTimeOffset τ k) (a+2*τ),
        jetSq (h t) k x≤localJetBound n K r τ σ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
        intro x hx t ht
        have hxO : x∈distBall (h a) p (2*r) := by simpa only [derivativeRadius_zero] using hx
        have htI : t∈Set.Icc a (a+2*τ) := by
          exact ⟨by simpa only [derivativeTimeOffset_zero,add_zero] using ht.1,ht.2.le⟩
        rw [localJetBound_zero,←curvatureJetNorm_sq]
        exact (sq_le_sq₀ (Real.sqrt_nonneg _) hK.le).mpr (hcurv x hxO t htI)
    | succ k =>
        intro q hq T hT
        let δ := derivativeTimeBuffer τ (k+1)
        let b₀ := T-δ
        let B := 1+localJetTotal n K r τ σ k
        have hδ : 0<δ := derivativeTimeBuffer_pos hτ (k+1)
        have hb₀ : a+derivativeTimeOffset τ k≤b₀ := by
          have he := derivativeTimeOffset_difference τ k
          dsimp only [b₀,δ]
          linarith [hT.1]
        have hab₀ : a≤b₀ :=
          (le_add_of_nonneg_right (derivativeTimeOffset_nonneg hτ k)).trans hb₀
        have hb₀T : b₀<T := by dsimp only [b₀]; linarith
        have hB : 1≤B := by dsimp only [B]; linarith [localJetTotal_nonneg n K r τ σ hK hr hτ hσ k]
        have hLower : ∀ x∈distBall (h a) p (derivativeRadius r k), ∀ t∈Set.Icc b₀ T,
            ∀ j≤k, jetSq (h t) j x≤B := by
          intro x hx t ht j hj
          have hrad := derivativeRadius_antitone hr hj
          have hxj : x∈distBall (h a) p (derivativeRadius r j) := by
            apply (mem_distBall_iff (h a) p x (derivativeRadius_pos hr j)).mpr
            exact ((mem_distBall_iff (h a) p x (derivativeRadius_pos hr k)).mp hx).trans_le hrad
          have htime := derivativeTimeOffset_monotone hτ hj
          have htj : t∈Set.Ico (a+derivativeTimeOffset τ j) (a+2*τ) :=
            ⟨by linarith [ht.1],ht.2.trans_lt hT.2⟩
          have hrec := ih j (by omega) x hxj t htj
          have hnum := localJetBound_le_total n K r τ σ hK hr hτ hσ hj
          exact hrec.trans (hnum.trans (by dsimp only [B]; linarith))
        have hsupport := hSupports k q hq b₀ T hab₀ hb₀T hT.2
        have hsupport' : ParabolicCutoffLowerSupports h σ
            (timeDistanceCutoff h q (Real.exp (-σ*(2*n : ℕ)*K*τ)*
              (derivativeRadius r k-derivativeRadius r (k+1))/4))
            (fieldDistanceBuffer (h a) p (derivativeRadius r (k+1)) (derivativeRadius r k)) b₀ T
            (16/(Real.exp (-σ*(2*n : ℕ)*K*τ)*
              (derivativeRadius r k-derivativeRadius r (k+1))/4)^2)
            (σ*(2*(2*n : ℕ)/(Real.exp (-σ*(2*n : ℕ)*K*τ)*
              (derivativeRadius r k-derivativeRadius r (k+1))/4)^2+
              (8/3 : ℝ)*(2*n : ℕ)*K)) := by
          simpa only [derivativeCutoffRadius_eq_buffer] using hsupport
        have hh := jet_distanceCutoff_bernstein_step h p q a K r τ σ
          (derivativeRadius r (k+1)) (derivativeRadius r k) b₀ T B hK hr hτ hσ
          hO hcO hflow hcurv (derivativeRadius_pos hr (k+1)) (derivativeRadius_succ_lt hr k)
          (derivativeRadius_le_two_mul hr k) hq hab₀ hb₀T hT.2 hB k hLower hsupport'
        rw [localJetBound_succ]
        convert hh using 1 <;> simp only [derivativeCutoffRadius_eq_buffer,B,b₀,sub_sub_cancel,δ]

theorem jetSq_core_closed_bound_of_cutoffSupports
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x∈distBall (h a) p (2*r), ∀ t∈Set.Icc a (a+2*τ), curvatureJetNorm (h t) 0 x≤K)
    (hSupports : DerivativeCutoffSupports h p a K r τ σ) (k : ℕ)
    (q : M.Carrier) (hq : q∈distBall (h a) p r) (T : ℝ) (hT : T∈Set.Icc (a+τ) (a+2*τ)) :
    jetSq (h T) k q≤localJetBound n K r τ σ k := by
  have hqk : q∈distBall (h a) p (derivativeRadius r k) := by
    apply (mem_distBall_iff (h a) p q (derivativeRadius_pos hr k)).mpr
    exact ((mem_distBall_iff (h a) p q hr).mp hq).trans (lt_derivativeRadius hr k)
  have hbound := jetSq_nested_bound_of_cutoffSupports h p a K r τ σ hK hr hτ hσ
    hO hcO hflow hcurv hSupports k q hqk
  by_cases hTb : T<a+2*τ
  · exact hbound T ⟨(by linarith [derivativeTimeOffset_lt hτ k,hT.1]),hTb⟩
  · have he : T=a+2*τ := le_antisymm hT.2 (le_of_not_gt hTb)
    rw [he]
    apply jetSq_bound_at_closed_right h a (a+2*τ) (a+τ) _ (by linarith) (by linarith)
      hflow.1 k q
    intro t ht
    exact hbound t ⟨(by linarith [derivativeTimeOffset_lt hτ k,ht.1]),ht.2⟩

end Yau.LeafProofs.L23Aux
