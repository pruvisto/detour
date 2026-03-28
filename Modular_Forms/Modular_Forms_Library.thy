(*<*)
section \<open>Auxiliary material\<close>
theory Modular_Forms_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "Algebraic_Numbers.Bivariate_Polynomials"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
begin

(* TODO: Move? *)
lemma continuous_within_poly2:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field}"
  assumes [continuous_intros]: "continuous (at F within A) f" "continuous (at F within A) g"
  shows "continuous (at F within A) (\<lambda>x. poly2 p (f x) (g x))"
  by (induction p) (auto intro!: continuous_intros continuous_within_poly)

lemma map_poly2_0 [simp]: "map_poly2 f 0 = 0"
  by (simp add: map_poly2_def)

lemma map_poly2_pCons [simp]:
  "p \<noteq> 0 \<or> q \<noteq> 0 \<Longrightarrow> map_poly2 f (pCons p q) = pCons (map_poly f p) (map_poly2 f q)"
  by (simp add: map_poly2_def)

lemma map_poly2_compose: "f 0 = 0 \<Longrightarrow> map_poly2 (f \<circ> g) p = map_poly2 f (map_poly2 g p)"
  by (rule poly_eqI) (auto simp: map_poly2_def coeff_map_poly map_poly_map_poly)
(* END TODO *)


(* TODO: Move *)
lemma has_fps_expansion_poly [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. poly p (f x)) has_fps_expansion (poly (map_poly fps_const p) F)"
  by (induction p) (auto intro!: fps_expansion_intros assms)

(* TODO Move *)
lemma has_fps_expansion_poly2 [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. poly2 p (f x) (g x)) has_fps_expansion (poly2 (map_poly2 fps_const p) F G)"
  by (induction p) (auto intro!: fps_expansion_intros assms simp: )

(* TODO Move *)
lemma fps_nth_numeral_pos [simp]: "n > 0 \<Longrightarrow> fps_nth (numeral m) n = 0"
  by (subst fps_numeral_nth) auto

(* TODO Move *)
lemma divisor_sigma_of_real: 
  "divisor_sigma (of_real s :: 'a :: nat_power_normed_field) n = of_real (divisor_sigma s n)"
  by (simp add: divisor_sigma_def)

(* TODO Move *)
lemma
  assumes "c \<in> \<real>"
  shows   Re_divisor_sigma_Reals [simp]: "Re (divisor_sigma c n) = divisor_sigma (Re c) n"
    and   Im_divisor_sigma_Reals [simp]: "Im (divisor_sigma c n) = 0"
  using assms by (auto elim!: Reals_cases simp: divisor_sigma_of_real)

(* TODO: Move *)
lemma has_laurent_expansion_imp_sums_complex:
  assumes f: "f analytic_on eball 0 r - {0}" "f has_laurent_expansion F"
  assumes z: "z \<in> eball 0 r - {0}"
  defines "n \<equiv> fls_subdegree F"
  shows   "(\<lambda>k. fls_nth F (int k + n) * z powi (int k + n)) sums f z"
proof -
  define F' where "F' = fls_base_factor_to_fps F"
  define f' where "f' = (\<lambda>z. if z = 0 then fps_nth F' 0 else f z * z powi - n)"
  have f': "f' has_fps_expansion F'"
    using has_fps_expansion_fls_base_factor_to_fps[OF f(2)] 
    by (simp add: F'_def n_def f'_def cong: if_cong)

  have ana: "f' analytic_on eball 0 r"
  proof -
    from f have "(\<lambda>z. f z * z powi -n) analytic_on eball 0 r - {0}"
      by (intro analytic_intros) auto
    hence "(\<lambda>z. f z * z powi -n) holomorphic_on eball 0 r - {0}"
      by (subst (asm) analytic_on_open) auto
    also have "?this \<longleftrightarrow> f' holomorphic_on eball 0 r - {0}"
      by (intro holomorphic_cong) (auto simp: f'_def)
    finally have "f' analytic_on eball 0 r - {0}"
      by (subst analytic_on_open) auto
    moreover have "f' analytic_on {0}"
      using f' by (simp add: has_fps_expansion_imp_analytic_0)
    ultimately have "f' analytic_on (eball 0 r - {0} \<union> {0})"
      by (subst analytic_on_Un) auto
    moreover have "eball 0 r \<subseteq> eball 0 r - {0} \<union> {0}"
      by blast
    ultimately show ?thesis
      using analytic_on_subset by blast
  qed

  have "(\<lambda>n. fps_nth F' n * z ^ n) sums f' z"
    by (rule has_fps_expansion_imp_sums_complex[where r = r])
       (use f' ana z in \<open>auto dest: analytic_imp_holomorphic\<close>)
  hence "(\<lambda>k. z powi n * (fps_nth F' k * z ^ k)) sums (z powi n * f' z)"
    by (intro sums_mult)
  also have "z powi n * f' z = f z"
    using z by (auto simp: f'_def power_int_minus)
  also have "(\<lambda>k. z powi n * (fps_nth F' k * z ^ k)) =
             (\<lambda>k. fls_nth F (int k + n) * z powi (int k + n))"
    using z by (simp add: F'_def n_def mult_ac power_int_add)
  finally show ?thesis .
qed

end
(*>*)