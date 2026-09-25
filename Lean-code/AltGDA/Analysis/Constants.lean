import AltGDA.Prelude

   
                                           

                                                                        
                                                                            
                            
  

namespace AltGDA

noncomputable section

theorem sqrt_two_pos : 0 < Real.sqrt 2 := by
  exact Real.sqrt_pos.2 (by norm_num)

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

theorem sqrt_two_lt_twenty_three_sixteenths :
    Real.sqrt 2 < (23 : ℝ) / 16 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := sqrt_two_sq
  nlinarith

theorem final_numeric_lt_fifteen :
    (12 : ℝ) + 2 * Real.sqrt 2 + 1 / 16 < 15 := by
  have hsqrt := sqrt_two_lt_twenty_three_sixteenths
  nlinarith

theorem final_numeric_identity :
    (12 : ℝ) + 2 * Real.sqrt 2 + 1 / 16 =
      193 / 16 + 2 * Real.sqrt 2 := by
  ring

theorem inv_two_sqrt_two_pos : 0 < (1 : ℝ) / (2 * Real.sqrt 2) := by
  positivity

theorem inv_two_sqrt_two_lt_half :
    (1 : ℝ) / (2 * Real.sqrt 2) < 1 / 2 := by
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := sqrt_two_sq
    nlinarith
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)
    (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem inv_two_sqrt_two_eq_sqrt_two_div_four :
    (1 : ℝ) / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  field_simp
  nlinarith [sqrt_two_sq]

                                                          
theorem final_expression_lt_fifteen {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ (1 : ℝ) / (2 * Real.sqrt 2)) :
    8 + (8 + 8 * Real.sqrt 2) * q + q ^ 2 / 2 < 15 := by
  have hq' : q ≤ Real.sqrt 2 / 4 := by
    rw [← inv_two_sqrt_two_eq_sqrt_two_div_four]
    exact hq
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlinear :
      (8 + 8 * Real.sqrt 2) * q ≤ 4 + 2 * Real.sqrt 2 := by
    have hcoef : 0 ≤ 8 + 8 * Real.sqrt 2 := by positivity
    have := mul_le_mul_of_nonneg_left hq' hcoef
    nlinarith [sqrt_two_sq]
  have hquad : q ^ 2 / 2 ≤ (1 : ℝ) / 16 := by
    have hsquare : q ^ 2 ≤ (Real.sqrt 2 / 4) ^ 2 := by nlinarith
    nlinarith [sqrt_two_sq]
  nlinarith [final_numeric_lt_fifteen]

end


end AltGDA
