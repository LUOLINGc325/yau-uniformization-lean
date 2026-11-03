import Yau.LeafProofs.L17GaussianSmallTime

noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L17Aux

theorem exists_common_nonlinear_scales {K ell : ℝ} (hK : 1≤K) (hell : 0<ell) :
    ∃ δ Ra Rb σ : ℝ, 0<δ ∧ δ≤1/8 ∧ 0<Ra ∧ 0<Rb ∧ 0<σ ∧ σ≤1 ∧
      8*K^4*δ≤1/4 ∧ K*Rb≤δ/4 ∧ K*Ra≤Rb/2 ∧ Rb≤ell/4 ∧
      ∀ (T : ℝ),0<T → T≤σ^2 → ∀ p : ℝ,1/2≤p →
        T≤1 ∧ 2*K*T^p≤δ/4 ∧ 3*K^4*T^p≤Ra/4 ∧ Rb+K*T≤ell/2 := by
  have hK0 : 0<K := zero_lt_one.trans_le hK
  let δ := min (1/8 : ℝ) (1/(32*K^4))
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  have hδ8 : δ≤1/8 := min_le_left _ _
  have hδK : 8*K^4*δ≤1/4 := by
    have h := (le_div_iff₀ (by positivity : 0<(32:ℝ)*K^4)).mp (min_le_right (1/8:ℝ) (1/(32*K^4)))
    change δ*(32*K^4)≤1 at h
    nlinarith
  let Rb := min (δ/(4*K)) (ell/4)
  have hRb : 0<Rb := lt_min (by positivity) (by positivity)
  have hRbell : Rb≤ell/4 := min_le_right _ _
  have hRbK : K*Rb≤δ/4 := by
    have h := (le_div_iff₀ (by positivity : 0<(4:ℝ)*K)).mp (min_le_left (δ/(4*K)) (ell/4))
    change Rb*(4*K)≤δ at h
    nlinarith
  let Ra := Rb/(2*K)
  have hRa : 0<Ra := by positivity
  have hRaK : K*Ra≤Rb/2 := by
    apply le_of_eq
    dsimp only [Ra]
    field_simp
  let σ := min (1:ℝ) (min (δ/(8*K)) (min (Ra/(12*K^4)) (ell/(4*K))))
  have hσ : 0<σ := lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hσ1 : σ≤1 := min_le_left _ _
  have hσδ : σ≤δ/(8*K) := (min_le_right _ _).trans (min_le_left _ _)
  have hσRa : σ≤Ra/(12*K^4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσell : σ≤ell/(4*K) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,Ra,Rb,σ,hδ,hδ8,hRa,hRb,hσ,hσ1,hδK,hRbK,hRaK,hRbell,?_⟩
  intro T hT hTs p hp
  have hT1 : T≤1 := hTs.trans (by nlinarith [hσ.le])
  have hSqrt : Real.sqrt T≤σ := by
    have h := Real.sqrt_le_sqrt hTs
    simpa only [Real.sqrt_sq hσ.le] using h
  have hTp : T^p≤Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hT hT1 hp
  have hTSqrt : T≤Real.sqrt T := by
    nlinarith [Real.sq_sqrt hT.le,Real.sqrt_nonneg T]
  have hδTime : 2*K*T^p≤δ/4 := by
    have hs := (le_div_iff₀ (by positivity : 0<(8:ℝ)*K)).mp ((hTp.trans hSqrt).trans hσδ)
    nlinarith
  have hRaTime : 3*K^4*T^p≤Ra/4 := by
    have hs := (le_div_iff₀ (by positivity : 0<(12:ℝ)*K^4)).mp ((hTp.trans hSqrt).trans hσRa)
    nlinarith
  have hellTime : K*T≤ell/4 := by
    have hs := (le_div_iff₀ (by positivity : 0<(4:ℝ)*K)).mp ((hTSqrt.trans hSqrt).trans hσell)
    nlinarith
  exact ⟨hT1,hδTime,hRaTime,by linarith⟩

end Yau.LeafProofs.L17Aux
